#! /usr/bin/env python

import sys, string, os, commands, shutil, re, subprocess
from math import sqrt, log10, log
from operator import itemgetter

def read_file1 (filename):
  fin=open(filename, 'r')
  fout=open("_tmp_"+filename, 'w')

  start = False

  for fin_buffer in fin:
    fin_flag = string.split(fin_buffer)
    if len(fin_flag) > 1 :
      if fin_flag[0] == "module" and fin_flag[1] == "type" and fin_flag[2] == "ATOM" and fin_flag[3] == "=":
        start = True
      if start == True:
        if len(fin_flag) > 1 :
  	  if fin_flag[0] == "type":
            if fin_flag[1] == "atom":
              fout.write ("  type atom = String.t\n")
	      start = False
            else:
              fout.write (fin_buffer)
          else:
            fout.write (fin_buffer)
        else:
          fout.write (fin_buffer)
      else:	      
        fout.write (fin_buffer)
    else:
      fout.write (fin_buffer)
        
  fin.close()
  fout.close()

  subprocess.Popen("mv _tmp_"+ filename + " "+ filename, shell=True, bufsize=8192, close_fds=True, stdout=None, stderr=None) 


def read_file2 (filename):
  fin=open(filename, 'r')
  fout=open("_tmp_"+filename, 'w')

  for fin_buffer in fin:
    fin_flag = string.split(fin_buffer)
    if len(fin_flag) > 4 :
      if fin_flag[0] == "mbind" and fin_flag[1] == "(fun" and fin_flag[2] == "x" and fin_flag[3] == "->" and fin_flag[4] == "x)":
              fout.write ("  Obj.magic (mbind (fun x -> x))\n")
      else:	      
        fout.write (fin_buffer)
    else:
      fout.write (fin_buffer)
        
  fin.close()
  fout.close()

  subprocess.Popen("mv _tmp_"+ filename + " "+ filename, shell=True, bufsize=8192, close_fds=True, stdout=None, stderr=None) 


# main 

read_file1 ("MetatheoryAtom.mli")
read_file1 ("MetatheoryAtom.ml")
read_file2 ("monad.ml")
