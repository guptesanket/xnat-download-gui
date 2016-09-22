#!/usr/bin/python
"""
Created on Thu Apr 21 16:58:38 2016

@author: Sanket Gupte

Xnat - Downloder BETA 2.0
"""


import sys
import os
import re
import dicom
import subprocess
import logging
import errno
import shutil
import time
from PyQt4 import QtCore, QtGui
from XnatUI import Ui_MainWindow
from pyxnat import Interface
from MySQLdb import connect
from string import whitespace

from sets import Set

import sip  #Used only for deleting layouts 
import threading 

#import XnatUtils as X
from dax import XnatUtils

XNAT_DOMAIN="https://xnaturl"

PROJ2RM =['000','Demographics']

#Pre-set destination path prefix
PATHPREFIX='/projects/%PROJ%'

#Pre-set filename Prefix
FILEPREFIX='%SCAN%'

#Pre-set ComboBox translations for Path Creation screen
CMBPATH=['PROJ','SUBJ','SESS','SCAN']
#Max number of parallel Processes for downloading
MAXPROC = 3

#Possible Conversion Programs used
CONVPROGS=['Dimon','to3d','dcm2nii','dcm2niix'] #NOT Implemeted yet, use the program if exists in path, in order of this precedence
#File names / File types that the conversion program makes, that you want ot delete
DELRESIDUE=['dimon.files.','GERT_Reco']

semaphore=threading.Semaphore(MAXPROC)

detail_logger = logging.getLogger('Xnat-Downloader')
hdlr = None
formatter = logging.Formatter('%(asctime)s %(levelname)s %(message)s')
logtype=0  # 1=Detailed ,0=Short


try:
    _fromUtf8 = QtCore.QString.fromUtf8
except AttributeError:
    def _fromUtf8(s):
        return s

try:
    _encoding = QtGui.QApplication.UnicodeUTF8
    def _translate(context, text, disambig):
        return QtGui.QApplication.translate(context, text, disambig, _encoding)
except AttributeError:
    def _translate(context, text, disambig):
        return QtGui.QApplication.translate(context, text, disambig)

# Memoise function to speed up things
def memoise(f):
    cache ={}
    return lambda *args: cache[args] if args in cache else cache.update({args: f(*args)}) or cache[args]


class StartQT(QtGui.QMainWindow):
    def __init__(self, parent=None):
        #Setting up the GUI
        QtCore.pyqtRemoveInputHook()
        QtGui.QWidget.__init__(self,parent)
        self.main_ui = Ui_MainWindow()
        self.main_ui.setupUi(self)
        
        # Connect signals to buttons
        # Main four buttons - Source, Destination, Download, Process
        QtCore.QObject.connect(self.main_ui.btn_page1,QtCore.SIGNAL("clicked()"),self.change_tab0)
        QtCore.QObject.connect(self.main_ui.btn_page2,QtCore.SIGNAL("clicked()"),self.change_tab1)
        QtCore.QObject.connect(self.main_ui.btn_page3,QtCore.SIGNAL("clicked()"),self.change_tab2)
        QtCore.QObject.connect(self.main_ui.btn_page4,QtCore.SIGNAL("clicked()"),self.change_tab3)
        # Top Buttons
        QtCore.QObject.connect(self.main_ui.btn_SignIn,QtCore.SIGNAL("clicked()"),self.click_signIn)
        QtCore.QObject.connect(self.main_ui.edt_pwd,QtCore.SIGNAL("returnPressed()"),self.click_signIn)
        QtCore.QObject.connect(self.main_ui.btn_log_browse,QtCore.SIGNAL("clicked()"),self.browse_clicked)
        QtCore.QObject.connect(self.main_ui.btn_refresh,QtCore.SIGNAL("clicked()"),self.refresh_xnat_conn)
        QtCore.QObject.connect(self.main_ui.btn_reset,QtCore.SIGNAL("clicked()"),self.reset_all)
        
        # Projects Combobox
        QtCore.QObject.connect(self.main_ui.cmb_project,QtCore.SIGNAL("currentIndexChanged(const QString&)"),self.index_proj_changed)
        
        # Subject, Session and Scan List/Tree connections
        QtCore.QObject.connect(self.main_ui.lst_subjects,QtCore.SIGNAL("itemChanged(QListWidgetItem *)"),self.click_sub)
        
        self.main_ui.tree_sessions.itemClicked.connect(self.handle_sess)
        #QtCore.QObject.connect(self.main_ui.tree_scans,QtCore.SIGNAL("itemChanged(QTreeWidgetItem *,int)"),self.click_scan)
        self.main_ui.tree_scans.itemClicked.connect(self.handle_scan)

        QtCore.QObject.connect(self.main_ui.btn_download,QtCore.SIGNAL("clicked()"),self.click_download)

        #Download Options Radio Button Signals
        QtCore.QObject.connect(self.main_ui.rb_afni, QtCore.SIGNAL("toggled(bool)"), self.afni_clicked)
        QtCore.QObject.connect(self.main_ui.rb_nifti, QtCore.SIGNAL("toggled(bool)"), self.nifti_clicked)
        QtCore.QObject.connect(self.main_ui.rb_custom, QtCore.SIGNAL("toggled(bool)"), self.custom_clicked)
        QtCore.QObject.connect(self.main_ui.rb_dcm, QtCore.SIGNAL("toggled(bool)"), self.dcm_clicked)
        
        #Path making Buttons
        QtCore.QObject.connect(self.main_ui.btn_send_edt,QtCore.SIGNAL("clicked()"),self.send2path_edt)
        QtCore.QObject.connect(self.main_ui.btn_send_cmb,QtCore.SIGNAL("clicked()"),self.send2path_cmb)
        QtCore.QObject.connect(self.main_ui.btn_reset_path_selected,QtCore.SIGNAL("clicked()"),self.reset_path_selected)
        QtCore.QObject.connect(self.main_ui.btn_reset_path_all,QtCore.SIGNAL("clicked()"),self.reset_path_all)
        
        #General Class Variables
        self.xnat_intf=None  #Xnat Interface
        self.curr_proj=None #Currently selected Xnat Project
                
        # Lists and Dictionaries
        self.li_subs=[] #List of subjects as received
        self.dict_checked_all={} #Dictionary of selected subjects
        
        self.tree_all={} # A dict of dict of dict for everything

        #For Destination Tab
        self.main_ui.grp_allScans=[]
        self.selected_uniq_scans={}      

        #For Download Tab        
        self.d_format=1  #1=DCM, 2=AFNI , 3=NIFTI, 4=CUSTOM
        self.download_begin=0  #Flag to start downloading
        
        #Initializations
        self.change_tab0()
        self.main_ui.edt_host.setText(XNAT_DOMAIN)
        self.main_ui.edt_username.setFocus()
        self.main_ui.tree_sessions.header().hide()
        self.main_ui.tree_scans.header().hide()
        self.main_ui.cmb_path_txt.addItems(CMBPATH)
        self.main_ui.rb_log_short.setChecked(True)
        

        
        #Set Cmd TextBox 
        #self.main_ui.edt_down_cmd.setText('%Output-Dir%/%File-Name%-######')
        self.main_ui.rb_dcm.setChecked(True)
        QtCore.QObject.connect(self.main_ui.btn_refresh_cmd,QtCore.SIGNAL("clicked()"),self.download_cmd_refresh)
        

        
    def handle_scan(self,item,column):
        #===========TODO==========
        #Handle the event : when all scans unchecked - disable the 'Download Tab' (btn_page2)
        self.main_ui.btn_page2.setEnabled(True)
        self.main_ui.tree_sessions.setEnabled(False)
        self.main_ui.lst_subjects.setEnabled(False)
        if item.checkState(column) == QtCore.Qt.Checked:  #Checked
            for child in range(item.childCount()):
                sess_det=self.lookup_session(item.child(child).text(0))
                del_keys=[]
                for k,v in self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][0].iteritems():
                    if item.text(0)==v:
                        del_keys.append(k)
                        #break  #There are scans with same name in some cases.
                #Pop from dict[0] and put it in dict[1] . 0=Unchecked , 1=Checked
                #self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][1]={x:self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][0].pop(x, None) for x in del_keys}
                self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][1].update({x:self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][0].pop(x, None) for x in del_keys})

        elif item.checkState(column) == QtCore.Qt.Unchecked:  #Unchecked
            for child in range(item.childCount()):
                sess_det=self.lookup_session(item.child(child).text(0))
                del_keys=[]
                for k,v in self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][1].iteritems():
                    if item.text(0)==v:
                        del_keys.append(k)
                        #break  #There are scans with same name in some cases.
                #Pop from dict[0] and put it in dict[1] . 0=Unchecked , 1=Checked
                
                #self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][0]={x:self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][1].pop(x, None) for x in del_keys}
                self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][0].update({x:self.dict_checked_all[str(sess_det[0])][str(item.child(child).text(0))][1][1].pop(x, None) for x in del_keys})

        else:
            pass #QtCore.Qt.PartiallyChekced
        
        
    def handle_sess(self, item, column):
        self.main_ui.lst_subjects.setEnabled(False)
        self.main_ui.tree_sessions.blockSignals(True)
        if item.checkState(column) == QtCore.Qt.Checked:  #Checked
            #print item.text(0)+ " Checked"
            if item.childCount()==0:
                sess_det =self.lookup_session(item.text(0)) #Get's subjID & scan details
                self.handle_sess_Chk(sess_det[0],item.text(0))
            else:
                for child in range(item.childCount()):
                    sess_det= self.lookup_session(item.child(child).text(0))  #Get's subjID & scan details
                    self.handle_sess_Chk(sess_det[0],item.child(child).text(0))
                    
        elif item.checkState(column) == QtCore.Qt.Unchecked:  #Unchecked
            #print item.text(0)+" Unchecked"
            if item.childCount()==0:
                sess_det =self.lookup_session(item.text(0)) #Get's subjID & scan details
                self.handle_sess_UnChk(sess_det[0],item.text(0))
            else:
                for child in range(item.childCount()):
                    sess_det= self.lookup_session(item.child(child).text(0))  #Get's subjID & scan details
                    self.handle_sess_UnChk(sess_det[0],item.child(child).text(0))
        self.main_ui.tree_sessions.blockSignals(False)
        

        
    def handle_sess_Chk(self,subj,sess):     
    
        if 'scans' not in self.tree_all[str(subj)][str(sess)]:
            tmp_sess_list=XnatUtils.list_scans(self.xnat_intf,str(self.curr_proj),str(subj),str(sess))
            self.tree_all[str(subj)][str(sess)]['scans']={}
            for scan in tmp_sess_list:
                self.tree_all[str(subj)][str(sess)]['scans'][scan['scan_id']]={k:v for k,v in scan.items() if k in ['scan_quality','scan_frames','scan_type']} #Getting only select things from the scan dict                
#        else :
#            pass
        for s_id,s_det in self.tree_all[str(subj)][str(sess)]['scans'].items():
            self.add_to_scan_tree(subj, sess,s_det['scan_type'])
            # Adding to dict_checked_all
            self.dict_checked_all[str(subj)][str(sess)][1][0][s_id]=s_det['scan_type']
            
        
    def add_to_scan_tree(self,subj,sess,scan):  # args are Non-Xnat terms/(labels not IDs)
        root=self.main_ui.tree_scans.invisibleRootItem()
        flag=0
        for index in range(root.childCount()):
            if root.child(index).text(0)==scan:
                new_kid=QtGui.QTreeWidgetItem(root.child(index))
                new_kid.setText(0,sess)
                new_kid.setStatusTip(0,subj)
                flag=1
                break
        if flag==0:
            parent = QtGui.QTreeWidgetItem(self.main_ui.tree_scans)
            parent.setText(0,scan)
            parent.setFlags(parent.flags() | QtCore.Qt.ItemIsUserCheckable)
            parent.setCheckState(0,QtCore.Qt.Unchecked)
            child = QtGui.QTreeWidgetItem(parent)
            child.setText(0,sess)
            child.setStatusTip(0,subj)
 
    def click_sub(self,item_sub):
        if item_sub.checkState(): #Item is Checked
            
            if str(item_sub.text()) not in self.tree_all:
                tmp_exp_list=XnatUtils.list_experiments(self.xnat_intf,str(self.curr_proj),str(item_sub.text()))
                self.tree_all[str(item_sub.text())]={}
                
                for exp in tmp_exp_list:                                        
                    self.tree_all[str(item_sub.text())][exp['label']]={}
                    self.tree_all[str(item_sub.text())][exp['label']]['exp']=exp['ID'] #Keeping only the ID  . No use for other fields for now.
                    self.tree_all[str(item_sub.text())][exp['label']]['strip']=self.strip_sub_id(str(item_sub.text()),exp['label'])
            
            self.dict_checked_all[str(item_sub.text())]={}
            for sess in self.tree_all[str(item_sub.text())]:                
                #self.dict_checked_all[str(item_sub.text())][sess]=[self.strip_sub_id(str(item_sub.text()),sess),{}] #Using the Processor
                self.dict_checked_all[str(item_sub.text())][sess]=[self.tree_all[str(item_sub.text())][sess]['strip'],{0: {}, 1: {}}] # 0= Not selected, 1=Selected scans

            root=self.main_ui.tree_sessions.invisibleRootItem()

            for sess in self.dict_checked_all[str(item_sub.text())]:
                flag=0
                for index in range(root.childCount()):
                    if root.child(index).text(0)==self.dict_checked_all[str(item_sub.text())][sess][0]:
                        new_kid=QtGui.QTreeWidgetItem(root.child(index))
                        new_kid.setFlags(new_kid.flags() | QtCore.Qt.ItemIsUserCheckable)
                        new_kid.setText(0,sess)
                        new_kid.setCheckState(0,QtCore.Qt.Unchecked)
                        flag=1
                        break
                if flag==0:
                    parent = QtGui.QTreeWidgetItem(self.main_ui.tree_sessions)
                    parent.setText(0,self.dict_checked_all[str(item_sub.text())][sess][0])
                    parent.setFlags(parent.flags()| QtCore.Qt.ItemIsTristate | QtCore.Qt.ItemIsUserCheckable)
                    #parent.setCheckState(0,QtCore.Qt.Unchecked)
                    child = QtGui.QTreeWidgetItem(parent)
                    child.setFlags(child.flags() | QtCore.Qt.ItemIsUserCheckable)
                    child.setText(0,sess)
                    child.setCheckState(0,QtCore.Qt.Unchecked)                        
                            
        else:
        
            sub=self.dict_checked_all.pop(str(item_sub.text()),None)
            #print sub
            root=self.main_ui.tree_sessions.invisibleRootItem()
            for sess in sub:
                #print sub[sess][0]
                for index in range(root.childCount()):
                    if root.child(index).text(0)==sub[sess][0]:
                        for ind2 in range(root.child(index).childCount()):
                            if root.child(index).child(ind2).text(0)==sess:
                                root.child(index).removeChild(root.child(index).child(ind2))
                                if root.child(index).childCount()==0:
                                    root.removeChild(root.child(index))
                                break
                        break

    def handle_sess_UnChk(self,subj,sess):
    
        for k_scan,v_scan in self.dict_checked_all[str(subj)][str(sess)][1][0].iteritems():
            self.remove_frm_scan_tree(str(subj),str(sess),v_scan)
        for k_scan,v_scan in self.dict_checked_all[str(subj)][str(sess)][1][1].iteritems():
            self.remove_frm_scan_tree(str(subj),str(sess),v_scan)
        self.dict_checked_all[str(subj)][str(sess)][1][0].clear() #Clearing UnSelected
        self.dict_checked_all[str(subj)][str(sess)][1][1].clear() #Clearing Selected
        
                

    def remove_frm_scan_tree(self,subj,sess,scan):  # args are Non-Xnat terms/(labels not IDs)
        root=self.main_ui.tree_scans.invisibleRootItem()
        
        for index in range(root.childCount()):
            if root.child(index).text(0)==scan:
                for ind2 in range(root.child(index).childCount()):
                    if root.child(index).child(ind2).text(0)==sess:
                        root.child(index).removeChild(root.child(index).child(ind2))
                        if root.child(index).childCount()==0:
                            root.removeChild(root.child(index))
                        break
                break

    def refresh_where(self):

        #-- Fresh
        vs_lay=QtGui.QVBoxLayout()

        vs_widg=QtGui.QWidget()
        vs_widg.setLayout(vs_lay)
        vs_scroll=QtGui.QScrollArea()
        vs_scroll.setWidgetResizable(True)
        vs_scroll.setWidget(vs_widg)
        
        self.reset_destination()

        
        for subj in self.dict_checked_all:
            for sess in self.dict_checked_all[subj]:
                for scan in self.dict_checked_all[subj][sess][1][1]: #Only Checked Scans
                    scan_name=self.dict_checked_all[subj][sess][1][1][scan]
                    if scan_name not in self.selected_uniq_scans:
                        self.selected_uniq_scans[scan_name]=''  #Save the text-box contents here
                        groupbox = QtGui.QGroupBox('%s' % scan_name)
                        groupbox.setCheckable(True)
                        grouplayout = QtGui.QVBoxLayout()
                        #grouptext = QtGui.QTextEdit()
#                        chkbox=QtGui.QCheckBox("Select")
#                        chkbox.setFixedWidth(400)
#                        chkbox.setFixedHeight(30)
                        txtpath=QtGui.QLineEdit(PATHPREFIX)
                        txtpath.setFixedWidth(650)
                        txtpath.setFixedHeight(30)
                        txtfname=QtGui.QLineEdit(FILEPREFIX)
                        txtfname.setFixedWidth(200)
                        txtfname.setFixedHeight(30)
                        chk_slice=QtGui.QCheckBox("Ignore Slice Chk")
                        chk_slice.setFixedHeight(30)
                        chk_db=QtGui.QCheckBox("Ignore Database Chk")
                        chk_db.setFixedWidth(150)
                        chk_db.setFixedHeight(30)
                        
                        
                        hbox1=QtGui.QHBoxLayout()
                        hbox2=QtGui.QHBoxLayout()
                        
                        #hbox1.addWidget(chkbox)
                        hbox1.addWidget(chk_slice)
                        hbox1.addWidget(chk_db)
                        hbox2.addWidget(txtpath)
                        hbox2.addWidget(txtfname)
                        
                        grouplayout.addLayout(hbox1)
                        grouplayout.addLayout(hbox2)
                        groupbox.setLayout(grouplayout)
                        vs_lay.addWidget(groupbox)
                        self.main_ui.grp_allScans.append(groupbox)
                

        layout=QtGui.QHBoxLayout()
        layout.addWidget(vs_scroll)
        self.main_ui.grp_path.setLayout(layout)

    def refresh_download(self):
# GETS EVERYTHING FROM THE DYNAMIC GroupBoxes 
#        for scan_grp in self.main_ui.grp_allScans:
#            print "^^^^^^^^^^^"
#            #Getting the GroupBoxes for each selected scan types
#            grp_layout=scan_grp.layout()
#            
#            #Getting hbox1 layout that has checkboxes
#            chk_layout=grp_layout.itemAt(0).layout()
#            print chk_layout.itemAt(0).widget().text()
#            print chk_layout.itemAt(1).widget().text()
#            
#            #Getting hbox2 layout that has the textboxes
#            txt_layout=grp_layout.itemAt(1).layout()
#            print txt_layout.itemAt(0).widget().text()
#            print txt_layout.itemAt(1).widget().text()

        self.reset_download()
        
        for scan_grp in self.main_ui.grp_allScans:
            
            #Getting the GroupBoxes for each selected scan types
            grp_layout=scan_grp.layout()

            self.selected_uniq_scans[str(scan_grp.title())]=[str(grp_layout.itemAt(1).layout().itemAt(0).widget().text()),str(grp_layout.itemAt(1).layout().itemAt(1).widget().text())]
        
        for subj in self.dict_checked_all:
            for sess in self.dict_checked_all[subj]:
                for scan in self.dict_checked_all[subj][sess][1][1]: #Only Checked Scans
                    scan_name=self.dict_checked_all[subj][sess][1][1][scan]
                    src_path="Proj:"+str(self.curr_proj)+"| Subj:"+str(subj)+"| Exp:"+str(sess)+"| Scan:"+str(scan_name)
                    #print src_path
                    int_path='/project/'+str(self.curr_proj)+'/subjects/'+str(subj)+'/experiments/'+str(sess)+'/scans/'+str(scan)
                    #print int_path
                    
                    dest_path=""
                    for dst_spl in [x for x in str(self.selected_uniq_scans[str(scan_name)][0]).split("%") if x]: #"%protocol%","%subject%","%session%","%scan%"
                        if dst_spl in ['proj','project','PROJ','PROJECT']:
                            dest_path+=str(self.curr_proj)
                        elif dst_spl in ["subject","subj","SUBJECT","SUBJ"]:
                            dest_path+=str(subj)
                        elif dst_spl in ["session","sess","SESSION","SESS"]:
                            dest_path+=str(sess)
                        elif dst_spl in ["scan","SCAN"]:
                            dest_path+=str(scan_name)
                        else:
                            dest_path+=str(dst_spl)
                    
                    dst_c_fn=""
                    for dst_fn in [x for x in str(self.selected_uniq_scans[str(scan_name)][1]).split("%") if x]:
                        if dst_fn in ['proj','project','PROJ','PROJECT']:
                            dst_c_fn+=str(self.curr_proj)
                        elif dst_fn in ["subject","subj","SUBJECT","SUBJ"]:
                            dst_c_fn+=str(subj)
                        elif dst_fn in ["session","sess","SESSION","SESS"]:
                            dst_c_fn+=str(sess)
                        elif dst_fn in ["scan","SCAN"]:
                            dst_c_fn+=str(scan_name)
                        else:
                            dst_c_fn+=dst_fn

                    
                    #Removing Whitespaces
                    dest_path=dest_path.translate(None,whitespace)
                    dst_c_fn=dst_c_fn.translate(None,whitespace)
                    dst_c_fn=dst_c_fn.replace('/','-')
                    dst_c_fn=dst_c_fn.replace('#','')
                    
                    #Add to lists 
                    itm_src=QtGui.QListWidgetItem(src_path)
                    itm_dest=QtGui.QListWidgetItem(dest_path)
                    itm_fname=QtGui.QListWidgetItem(dst_c_fn)
                    
                    itm_src.setFlags(itm_src.flags() | QtCore.Qt.ItemIsEditable)                    
                    itm_dest.setFlags(itm_dest.flags() | QtCore.Qt.ItemIsEditable)
                    itm_fname.setFlags(itm_fname.flags() | QtCore.Qt.ItemIsEditable)
                    
                    #itm_dest.setData(1,QtCore.QVariant(int_path))
                    itm_dest.setToolTip(int_path)
                    
                    
                    
                    self.main_ui.lst_sel_log.addItem(itm_src)
                    self.main_ui.lst_dest_pick.addItem(itm_dest)
                    self.main_ui.lst_filename.addItem(itm_fname)
                    
                    self.download_cmd_refresh()


    def check_path_unique(self):
        path_list=[]
        for i in range(self.main_ui.lst_dest_pick.count()):
            path_list.append(self.main_ui.lst_dest_pick.item(i).text()+'/'+self.main_ui.lst_filename.item(i).text())
        #print path_list
        #print set(path_list)
        if len(path_list)>len(set(path_list)):
            self.PopupDlg("Duplicate download destinations found. Make unique Paths !!")
            return 0
        else:
            return 1
    
            

    def afni_clicked(self):
        #AFNI MPRage
        #lst_cmd=['Dimon','-infile_pattern','%Output-Dir%'+'/*','-dicom_org','-gert_create_dataset','-gert_to3d_prefix','%File-Name%','-gert_outdir','%Output-Dir%']
    
        #AFNI Non-MPRage
        #lst_cmd=['Dimon','-infile_pattern','%Output-Dir%'+'/*','-dicom_org','-gert_create_dataset','-gert_to3d_prefix','%File-Name%','-gert_outdir','%Output-Dir%']
        self.d_format=2
        if self.prog_exists('Dimon'):
            self.main_ui.edt_down_cmd.setText('Dimon -infile_pattern %Output-Dir%/* -dicom_org -gert_create_dataset -gert_to3d_prefix %File-Name% -gert_outdir %Output-Dir%')
            self.main_ui.edt_down_status.setText("Status: Please confirm the arguments to Dimon")
            self.main_ui.edt_down_status.setStyleSheet("color: rgb(128,128,0);")
        else:
            self.main_ui.edt_down_cmd.setText('<Custom Program> -LocOfDcmFiles %Output-Dir%/* -CustomFileExtension %File-Name% -CustomFileDOwnloadLocation %%Output-Dir%/Custom')
            self.main_ui.edt_down_status.setText("Status: Dimon not found. Please Enter proper conversion command")
            self.main_ui.edt_down_status.setStyleSheet("color: rgb(255,0,0);")
        self.download_cmd_refresh()
    
    def nifti_clicked(self):
        #NIFTI MPRage
        #lst_cmd=['Dimon','-infile_pattern','%Output-Dir%')+'/*','-dicom_org','-gert_create_dataset','-gert_write_as_nifti','-gert_to3d_prefix','%File-Name%','-gert_outdir','%Output-Dir%']
        
        #NIFTI Non-MPRage
        #lst_cmd=['Dimon','-infile_pattern','%Output-Dir%'+'/*','-dicom_org','-gert_create_dataset','-gert_write_as_nifti','-gert_to3d_prefix','%File-Name%','-gert_outdir','%Output-Dir%']
        self.d_format=3
        if self.prog_exists('Dimon'):
            self.main_ui.edt_down_cmd.setText('Dimon -infile_pattern %Output-Dir%/* -dicom_org -gert_create_dataset -gert_write_as_nifti -gert_to3d_prefix %File-Name% -gert_outdir %Output-Dir%')
            self.main_ui.edt_down_status.setText("Status: Please confirm the arguments to Dimon")
            self.main_ui.edt_down_status.setStyleSheet("color: rgb(128,128,0);")
        else:
            self.main_ui.edt_down_cmd.setText('<Custom Program> -LocOfDcmFiles %Output-Dir%/* -CustomFileExtension %File-Name% -CustomFileDOwnloadLocation %%Output-Dir%/Custom')
            self.main_ui.edt_down_status.setText("Status: Dimon not found. Please Enter proper conversion command")
            self.main_ui.edt_down_status.setStyleSheet("color: rgb(255,0,0);")            
        self.download_cmd_refresh()
        
    
    def custom_clicked(self):
        self.d_format=4
        if self.prog_exists('dcm2nii'):
            self.main_ui.edt_down_cmd.setText('dcm2nii -e N -f Y -d N -p N -v N -g N %Output-Dir%/%File-Name%')
            self.main_ui.edt_down_status.setText("Status: Please confirm the arguments to dcm2nii are correct")
            self.main_ui.edt_down_status.setStyleSheet("color: rgb(255,140,0);")
        else:
            self.main_ui.edt_down_cmd.setText('<Custom Program> -LocOfDcmFiles %Output-Dir%/* -CustomFileExtension %File-Name% -CustomFileDOwnloadLocation %%Output-Dir%/Custom')
            self.main_ui.edt_down_status.setText("Status: Please Enter proper conversion command")
            self.main_ui.edt_down_status.setStyleSheet("color: rgb(255,0,0);")
        self.download_cmd_refresh()
    
    def dcm_clicked(self):
        self.d_format=1
        self.main_ui.edt_down_status.setText("Status: Ready. No Conversion needed")
        self.main_ui.edt_down_cmd.setText('%Output-Dir%/%File-Name%-######')
        self.main_ui.edt_down_status.setStyleSheet("color: rgb(107,142,35);")
        self.download_cmd_refresh()
    
    def download_cmd_refresh(self):
        #Make FUll Command in the ListWidget
        self.main_ui.lst_cmd.clear()
        for subj in self.dict_checked_all:
            for sess in self.dict_checked_all[subj]:
                for scan in self.dict_checked_all[subj][sess][1][1]: #Only Checked Scans
                    itm_cmd=QtGui.QListWidgetItem(self.main_ui.edt_down_cmd.text())
                    itm_cmd.setFlags(itm_cmd.flags() | QtCore.Qt.ItemIsEditable)
                    self.main_ui.lst_cmd.addItem(itm_cmd)
                    
    def prog_exists(self,prog_name): #Checking if the program exists in the environment
        try:
            devnull = open(os.devnull)
            subprocess.Popen([prog_name],stdout=devnull,stderr=devnull).communicate()
        except OSError as e:
            if e.errno == os.errno.ENOENT:
                return False
        return True

    def click_download(self):
        if self.check_path_unique()==0:
            return
        
        if self.DownloadMsgBox(self.d_format)==1024: #1024 = 0x00000400  , the message sent when OK is pressed
            global hdlr
            global detail_logger
            global formatter
            global logtype

            #Starting Download Disabling button             
            self.main_ui.btn_download.setEnabled(False)

            hdlr = logging.FileHandler(str(self.main_ui.edt_log_path.text()))
            hdlr.setFormatter(formatter)
            detail_logger.addHandler(hdlr)
            detail_logger.setLevel(logging.DEBUG)
            detail_logger.info('Beginning download.......')
            if self.main_ui.rb_log_detailed.isChecked():
                logtype=1
            #print "Download Starting !" #Start Download Process
            threads=[]
            for i in range(self.main_ui.lst_cmd.count()):
                detail_logger.info(str(i+1)+" : "+str(self.main_ui.lst_sel_log.item(i).text()))
                thread = DownloadThread(self.myargs,self.d_format,self.main_ui.lst_dest_pick.item(i).text(),self.main_ui.lst_filename.item(i).text(),self.main_ui.lst_dest_pick.item(i).toolTip(),self.main_ui.lst_cmd.item(i).text(),str(i+1),self.main_ui.lst_cmd.count())
                threads.append(thread)
                #print self.main_ui.lst_cmd.item(i).text()
            for t in threads:
                t.start()
                
            for t in threads:                
                t.join()
                
            self.PopupDlg("Download Finished !!")
            self.main_ui.btn_download.setEnabled(True)
    

    def send2path_edt(self):
        if self.main_ui.rb_send_path.isChecked():
                
            for scan_grp in self.main_ui.grp_allScans:
                #Getting the GroupBoxes for each selected scan types
                if scan_grp.isChecked():
                    grp_layout=scan_grp.layout()
                
    #            #Getting hbox1 layout that has checkboxes
    #            chk_layout=grp_layout.itemAt(0).layout()
    #            print chk_layout.itemAt(0).widget().text()
    #            print chk_layout.itemAt(1).widget().text()
                
                #Getting hbox2 layout that has the textboxes
                    txt_layout=grp_layout.itemAt(1).layout()
                    txt_layout.itemAt(0).widget().setText(txt_layout.itemAt(0).widget().text()+self.main_ui.edt_path_txt.text())
                    
        elif self.main_ui.rb_send_file.isChecked():
                            
            for scan_grp in self.main_ui.grp_allScans:
                #Getting the GroupBoxes for each selected scan types
                if scan_grp.isChecked():
                    grp_layout=scan_grp.layout()
                
    #            #Getting hbox1 layout that has checkboxes
    #            chk_layout=grp_layout.itemAt(0).layout()
    #            print chk_layout.itemAt(0).widget().text()
    #            print chk_layout.itemAt(1).widget().text()
                
                #Getting hbox2 layout that has the textboxes
                    txt_layout=grp_layout.itemAt(1).layout()
                    txt_layout.itemAt(1).widget().setText(txt_layout.itemAt(1).widget().text()+self.main_ui.edt_path_txt.text())
        else:
            self.PopupDlg("Please Select WHERE to send this text !")
    

    def send2path_cmb(self):
        if self.main_ui.rb_send_path.isChecked():
                
            for scan_grp in self.main_ui.grp_allScans:
                #Getting the GroupBoxes for each selected scan types
                if scan_grp.isChecked():
                    grp_layout=scan_grp.layout()
               
                #Getting hbox2 layout that has the textboxes
                    txt_layout=grp_layout.itemAt(1).layout()
                    txt_layout.itemAt(0).widget().setText(txt_layout.itemAt(0).widget().text()+"%"+str(self.main_ui.cmb_path_txt.currentText())+"%")
                    
        elif self.main_ui.rb_send_file.isChecked():
                            
            for scan_grp in self.main_ui.grp_allScans:
                #Getting the GroupBoxes for each selected scan types
                if scan_grp.isChecked():
                    grp_layout=scan_grp.layout()

                #Getting hbox2 layout that has the textboxes
                    txt_layout=grp_layout.itemAt(1).layout()
                    txt_layout.itemAt(1).widget().setText(txt_layout.itemAt(1).widget().text()+"%"+str(self.main_ui.cmb_path_txt.currentText())+"%")
        else:
            self.PopupDlg("Please Select WHERE to send this text !")



    def reset_path_selected(self):
# GETS EVERYTHING FROM THE DYNAMIC GroupBoxes 
        for scan_grp in self.main_ui.grp_allScans:
            #Getting the GroupBoxes for each selected scan types
            if scan_grp.isChecked():
                grp_layout=scan_grp.layout()
                        
            #Getting hbox2 layout that has the textboxes
                txt_layout=grp_layout.itemAt(1).layout()
                txt_layout.itemAt(0).widget().setText("")
                txt_layout.itemAt(1).widget().setText("")
    
    def reset_path_all(self):
# GETS EVERYTHING FROM THE DYNAMIC GroupBoxes 
        for scan_grp in self.main_ui.grp_allScans:
            #Getting the GroupBoxes for each selected scan types
            #print scan_grp.isChecked()
            grp_layout=scan_grp.layout()
            
#            #Getting hbox1 layout that has checkboxes
#            chk_layout=grp_layout.itemAt(0).layout()
#            print chk_layout.itemAt(0).widget().text()
#            print chk_layout.itemAt(1).widget().text()
            
            #Getting hbox2 layout that has the textboxes
            txt_layout=grp_layout.itemAt(1).layout()
            txt_layout.itemAt(0).widget().setText("")
            txt_layout.itemAt(1).widget().setText("")
    
    
    def refresh_process(self):
        pass

           
    @memoise
    def lookup_session(self,sess):
        
        for k_sub, v_sess in self.dict_checked_all.iteritems():
            for k_sess, v_scans in v_sess.iteritems():
                if k_sess==sess:
                    return(k_sub,v_scans)
        return None
        

    def change_tab0(self): #Source
        self.main_ui.stackedWidget.setCurrentIndex(0)
        self.reset_process()
        self.reset_download()
        self.reset_destination()
    def change_tab1(self): #Destination
        self.main_ui.stackedWidget.setCurrentIndex(1)
        self.reset_process()
        self.reset_download()
        self.refresh_where()
        self.main_ui.btn_page3.setEnabled(True)
    def change_tab2(self): #Download
        self.main_ui.stackedWidget.setCurrentIndex(2)
        self.reset_process()
        self.refresh_download()
        self.main_ui.btn_page4.setEnabled(True)
        
    def change_tab3(self): #Process
        self.main_ui.stackedWidget.setCurrentIndex(3)
        self.refresh_process()

    def reset_source(self):
        self.main_ui.lst_subjects.clear()
        del self.li_subs[:]
        self.dict_checked_all.clear()
        self.tree_all.clear()
        self.main_ui.tree_sessions.clear()
        self.main_ui.tree_scans.clear()
        self.main_ui.lst_subjects.setEnabled(True)
        

    def reset_destination(self):
        #Removing the created layouts. For Layman-proofing the GUI
#        for scan_grp in self.main_ui.grp_allScans:
#            for i in reversed(scan_grp.layout().count()):
#                scan_grp.layout().itemAt(i).widget().setParent(None)
        self.delete_layout(self.main_ui.grp_path.layout())
        self.selected_uniq_scans.clear()
        del self.main_ui.grp_allScans[:] #Deleting contents of the list
        

    def reset_download(self):
        self.main_ui.lst_sel_log.clear()
        self.main_ui.lst_dest_pick.clear()
        self.main_ui.lst_filename.clear()
        self.main_ui.lst_cmd.clear()
    
    def reset_process(self):
        pass

    def reset_internal(self):
        self.reset_process()
        self.main_ui.btn_page4.setEnabled(False)
        self.reset_download()
        self.main_ui.btn_page3.setEnabled(False)
        self.reset_destination()
        self.main_ui.btn_page2.setEnabled(False)
        self.reset_source()
        
        

    def reset_all(self):
        self.refresh_xnat_conn()
        self.get_projects()
        self.main_ui.tree_sessions.setEnabled(True)
        self.main_ui.lst_subjects.setEnabled(True)
        #self.curr_proj=self.main_ui.cmb_project.currentText()
        self.change_tab0()
        self.reset_internal()
            
            
    def populate_subjects(self):
        if self.main_ui.cmb_project.currentIndex()!=0:
            self.li_subs.extend(XnatUtils.list_subjects(self.xnat_intf,str(self.curr_proj)))
            # Populate the Subject List
            for sub in self.li_subs:
                tmp_item=QtGui.QListWidgetItem(sub['label'])
                tmp_item.setToolTip(sub['ID'])
                tmp_item.setCheckState(0)
                self.main_ui.lst_subjects.addItem(tmp_item)
    
    
    def index_proj_changed(self):
        self.curr_proj=self.main_ui.cmb_project.currentText()
        self.reset_internal()
        self.populate_subjects()
 
    def get_projects(self):
        self.main_ui.cmb_project.clear()
        ls_prot=[]
        try:
            full_projs= XnatUtils.list_projects(self.xnat_intf)
        except:
            self.PopupDlg("Please check the Username and Password")
        else:
            ls_prot.append("-----Select-----")
            for proj in full_projs:
                ls_prot.append(proj['ID'])
            
            #Hard-coded removing some projects
            global PROJ2RM
            for prj in PROJ2RM:
                try :                    
                    ls_prot.remove(str(prj))                    
    #                ls_prot.remove('000')
    #                ls_prot.remove('Demographics')
    #                ls_prot.remove('')
                except:
                    pass
            
            self.main_ui.cmb_project.addItems(ls_prot)
            self.main_ui.lbl_status.setVisible(True)
            self.main_ui.lbl_status.setStyleSheet(_fromUtf8("background-color:#4d9900;"))
            self.main_ui.lbl_status.setText('SUCCESS')
        finally:
            self.main_ui.edt_pwd.setText("")
            
       
    def refresh_xnat_conn(self):
        try:
            self.xnat_intf.disconnect()
        except:
                pass
        self.xnat_intf=Interface(**self.myargs)
        
    def click_signIn(self):
        host=str(self.main_ui.edt_host.text())
        uname=str(self.main_ui.edt_username.text())
        passwd=str(self.main_ui.edt_pwd.text())
        xcache=os.path.expanduser("~")+"/.xnat_cache"
        
        if host=="" or uname=="" or passwd=="":
            self.PopupDlg("Please Enter all information !!")
        else:
            if os.path.exists(xcache):
                shutil.rmtree(xcache)
            if not os.path.exists(xcache):
                    try:
                        os.makedirs(xcache)
                    except os.error, e:
                        if e.errno != errno.EEXIST:
                            raise
    
            self.myargs={'server':host,'user':uname,'password':passwd,'cachedir':xcache}#, 'verify':False}
        self.main_ui.edt_log_path.setText(xcache+"/XnatDownload_"+time.strftime("%Y%m%d-%H%M%S")+".log")
        self.reset_all()

        

        
    def strip_sub_id(self,subj,sess):
        return str(str(sess).replace(str(subj),"").strip('-').strip('_').strip('(').strip(')'))
    def strip_tail(self,str_strip):
        return str(str_strip).split("(")[0]
        
    def browse_clicked(self):
        txt=QtGui.QFileDialog.getOpenFileName()
        if self.BrowseFileMsgBox()==1024: # Ok Clicked
            self.main_ui.edt_log_path.setText(txt)

    def PopupDlg(self,msg_show):
        self.dlg=MyPopupDlg(msg_show)
        self.dlg.exec_()  #For modal dialog

    def closeEvent(self,event):
        result = QtGui.QMessageBox.question(self,
                      "Confirm Exit...",
                      "Are you sure you want to exit ?",
                      QtGui.QMessageBox.Yes| QtGui.QMessageBox.No)
        event.ignore()

        if result == QtGui.QMessageBox.Yes:
            try:
                self.xnat_intf.disconnect()   #Disconnect the Xnat Interface before exiting
            except:
                pass
            event.accept()

    def delete_layout(self,layout):
        if layout is not None:
            while layout.count():
                item = layout.takeAt(0)
                widget = item.widget()
                if widget is not None:
                    widget.deleteLater()
                else:
                    self.deleteLayout(item.layout())
            sip.delete(layout)


    def BrowseFileMsgBox(self):
        msg = QtGui.QMessageBox()
        msg.setIcon(QtGui.QMessageBox.Information)
        msg.setText("File will be overwritten")
        msg.setWindowTitle("File Overwrite")
        msg.setStandardButtons(QtGui.QMessageBox.Ok | QtGui.QMessageBox.Cancel)
        return msg.exec_()
        
    def DownloadMsgBox(self,dformat):
       if dformat==1:
           dfformat='DICOM'
       elif dformat==2:
           dfformat='AFNI'
       elif dformat==3:
           dfformat='NIFTI'
       elif dformat==4:
           dfformat='CUSTOM'
       msg = QtGui.QMessageBox()
       msg.setIcon(QtGui.QMessageBox.Information)
       msg.setText("READY ??")
       msg.setInformativeText("All scans will be downloaded in %s format" %(dfformat))
       msg.setWindowTitle("Begin Download")
       msg.setDetailedText("Do not close the main window until you see the Finish window. \nCheck the progress bar for status.\nAfter all is done, Check the Log for any problems during download or conversion")
       msg.setStandardButtons(QtGui.QMessageBox.Ok | QtGui.QMessageBox.Cancel)
       #msg.buttonClicked.connect(self.MsgBoxBtn)
       return msg.exec_()
       #retval = msg.exec_()
       #print "value of pressed messge box button:", retval
#    def MsgBoxBtn(self,btn):
#        if btn.text()=="OK":
#            self.download_begin=1


class MyPopupDlg(QtGui.QDialog):
    def __init__(self,msg,parent=None):
        #self.resize(300,200)
        super(MyPopupDlg, self).__init__(parent)
        layout=QtGui.QGridLayout(self)
        lbl=QtGui.QLabel(msg)
        #btn=QtGui.QPushButton("Ok")
        btn=QtGui.QDialogButtonBox(QtGui.QDialogButtonBox.Ok,QtCore.Qt.Horizontal,self)
        btn.accepted.connect(self.accept)
        layout.addWidget(lbl)
        layout.addWidget(btn)

def real_download(xnat_args,d_format,fs_path,fs_fname,xnat_path,cmd,downld_no,downld_tot):
    with semaphore:
        global logtype
        global detail_logger
        xnat_intf=Interface(**xnat_args)
        detail_logger.info('Downloading: '+str(downld_no)+' of '+str(downld_tot))
        if logtype==1:
            detail_logger.info("Downloading >>"+str(xnat_path))
        #print "Downloading: "+str(xnat_path)
        res_count=0  #Resource count
        dcm_count=0  #Number of resources with Dicoms in it
        for r in xnat_intf.select(str(xnat_path)).resources().get():
            res_count+=1
            if logtype==1:
                detail_logger.info("Looking for files in resource: "+str(res_count))
            lst_files=xnat_intf.select(str(xnat_path)).resource(str(r)).files().get()
#            if len(lst_files)==0:
#                print "Got Empty Resource"
#                continue
            
            dcm_flag=0
            for ff in lst_files:
                if str(ff)[-3:]=='dcm':
                    dcm_flag=1
                    dcm_count+=1
                    if logtype==1:
                        detail_logger.info("Found Dicom files !")
                    break
            if dcm_flag==0:  #Going to next iteration since this resource doesn't have dicoms
                if logtype==1:
                    detail_logger.info("No Dicom Files Found !")
                continue
            
            #Create directories if they dont exist
            #Append number in directory name, if there are multiple resources with dcm files.
            if res_count>1 and dcm_count>1:
                if logtype==1:
                    detail_logger.info("Multiple Resources with Dicom files")
                tmp_dir=str(fs_path)+str(res_count)+'/'
            else:
                tmp_dir=str(fs_path)+'/'
            dir_success=1   #Assuming creating directory was a success, unless otherwise changed
            if not os.path.exists(tmp_dir):
                try:
                    detail_logger.info("Creating Directories if needed")
                    os.makedirs(tmp_dir)
                except os.error, e:
                    if e.errno ==errno.EEXIST:
                        #raise     #Only raises errors that are not of the type File exist (Redundant check)
                        #print "Path already Exists. No need to create it."
                        pass

                    elif e.errno ==13:
                        dir_success=0
                        detail_logger.error("You do not have permission to create this directory")
                        #print "You do not have permission to create this directory"
                    else:
                        #print "Something went wrong with creating this directory"
                        dir_success=0
                        detail_logger.error("Something went wrong with Creating this directory this directory")
                        detail_logger.error(str(e.errno))
                        detail_logger.error(str(e.message))
                    
            #Getting Files if directory creation was a success
            if dir_success==1:
                #Getting Each file individually and renaming it
                i=0
                if len(lst_files)==1:  #When there is only 1 dicom file. Usually in case of single mosaics
                    if str(lst_files[0])[-3:]=='dcm':  #Getting only DICOM file
                        full_path=tmp_dir+str(fs_fname)+'.dcm'
                        xnat_intf.select(str(xnat_path)).resource(str(r)).file(str(ff)).get(full_path)
                        if logtype==1:
                            detail_logger.info("Fetched Single File > "+str(ff))
                else:
                    for ff in lst_files:
                        if str(ff)[-3:]=='dcm':  #Getting only DICOM files
                            i+=1
                            full_path=tmp_dir+str(fs_fname)+'-{:0>10}'.format(str(i)+'.dcm')
                            xnat_intf.select(str(xnat_path)).resource(str(r)).file(str(ff)).get(full_path)
                            if logtype==1:
                                detail_logger.info("Fetched File > "+str(ff))

                    

                detail_logger.info("All Dicom Files Downloaded")
                #Dicom Files downloaded now conversion

                #Convert files and then Delete the dicoms
                if d_format!=1: #Download format is not dcm
                    #Combining 3 statements into 1 line.
                    lst_cmd=str(str(cmd).replace('%Output-Dir%',fs_path)).replace('%File-Name%',fs_fname).split()
                    
                    detail_logger.info("Beginning Conversion-------------")
                    proc=subprocess.Popen(lst_cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
                    # Do things here, while it's converting.
                    outs, err=proc.communicate()
                    #proc.wait()
                    if logtype==1:
                        detail_logger.info("Output: "+str(outs))
                    detail_logger.error("Error: " + str(err))
                    
                    #Deleting dcm files
                    for f in os.listdir(tmp_dir):
                        if str(f)[-3:]=='dcm':
                            os.remove(os.path.join(tmp_dir,f))

            else:
                detail_logger.error("Files were  not downloaded due to directory creation failure")
        #Deleting Extra Files
        global DELRESIDUE
        for ft in DELRESIDUE:
            for f in os.listdir(os.getcwd()):
                if re.search(ft,f):
                    os.remove(os.path.join(os.getcwd(),f))
                    if logtype==1:
                        detail_logger.info(str(ft)+" type of files deleted !")


        
        #Close Xnat Connection
        try:
            xnat_intf.disconnect()
        except:
            pass
        #return os.system(command-to-run)
        

class DownloadThread(threading.Thread):
    def __init__(self,xnat_args,d_format,fs_path,fs_fname,xnat_path,cmd,downld_no,downld_tot):
        threading.Thread.__init__(self)
        self.xnat_args=xnat_args
        self.d_format=d_format
        self.fs_path = fs_path
        self.fs_fname = fs_fname
        self.xnat_path = xnat_path
        self.cmd=cmd
        self.downld_no=downld_no
        self.downld_tot=downld_tot
        
    def run(self):
        real_download(self.xnat_args,self.d_format,self.fs_path,self.fs_fname,self.xnat_path,self.cmd,self.downld_no,self.downld_tot)
        
if __name__ == "__main__":
    
    app = QtGui.QApplication.instance() #Checks if QApplication already exists    
    if not app:
        app = QtGui.QApplication(sys.argv)
    myapp = StartQT()
    app_icon=QtGui.QIcon()
    app_icon.addFile('icons/brain_16_icon.ico',QtCore.QSize(16,16))
    app_icon.addFile('icons/brain_24_icon.ico',QtCore.QSize(24,24))
    app_icon.addFile('icons/brain_32_icon.ico',QtCore.QSize(32,32))
    app_icon.addFile('icons/brain_48_icon.ico',QtCore.QSize(48,48))
    app_icon.addFile('icons/brain_64_icon.ico',QtCore.QSize(64,64))
    app_icon.addFile('icons/brain_128_icon.ico',QtCore.QSize(128,128))
    app_icon.addFile('icons/brain_192_icon.ico',QtCore.QSize(192,192))
    app_icon.addFile('icons/brain_256_icon.ico',QtCore.QSize(256,256))
    app_icon.addFile('icons/brain_96_icon.ico',QtCore.QSize(96,96))
    myapp.setWindowIcon(app_icon)
    myapp.show()
    sys.exit(app.exec_())
