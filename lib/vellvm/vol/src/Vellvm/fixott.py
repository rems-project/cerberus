#! /usr/bin/env python

import sys, string, os, commands, shutil, re, subprocess
from math import sqrt, log10, log
from operator import itemgetter

def read_file():
  if len (sys.argv) > 1:
    infname = sys.argv[1]
  else:
    infname = "ssa.v"

  outfname = "_tmp_" + infname

  fin=open(infname, 'r')
  fout=open(outfname, 'w')

  for fin_buffer in fin:
    fin_flag = string.split(fin_buffer)
    if len(fin_flag) > 4 :
      if fin_flag[0] == "|" and fin_flag[1] == "0," and fin_flag[2] == "other" and fin_flag[3] == "=>" and fin_flag[4] == "None":	    
	fout.write ("  | O, other => None\n")
      else:
        if fin_flag[0] == "|" and fin_flag[1] == "0," :	    
          if string.find (fin_flag[2], "Cons_list_") != -1:		   
            fin_flag[1] = "O,"		   
	    out_str = "  "
	    for s in fin_flag:
              out_str += s
              out_str += " "
	    out_str += "\n"
            fout.write (out_str)	    
          else:		   
            fout.write (fin_buffer)
        else:
          fout.write (fin_buffer)
    else:
      fout.write (fin_buffer)
        
  fin.close()
  fout.close()

  subprocess.Popen("mv "+ outfname + " "+ infname, shell=True, bufsize=8192, close_fds=True, stdout=None, stderr=None) 
# main 

read_file()
