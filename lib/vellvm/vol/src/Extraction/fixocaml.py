#! /usr/bin/env python

import sys, string, os, commands, shutil, re
from math import sqrt, log10, log
from operator import itemgetter

def read_file():
  fin=open("symexe.mli", 'r')
  fout=open("_tmp_symexe.mli", 'w')

  start = False

  for fin_buffer in fin:
    fin_flag = string.split(fin_buffer)
    if len(fin_flag) > 1 :
      if fin_flag[0] == "module" and fin_flag[1] == "LLVMsyntax":
        start = True
      if start == True:
        if len(fin_flag) > 3 :
  	  if fin_flag[0] == "type":
            if fin_flag[1] == "coq_INT" and fin_flag[2] == "=":
              fout.write ("  type coq_INT = Llvm.llapint\n")
            elif fin_flag[1] == "id"  and fin_flag[2] == "=":
              fout.write ("  type id = String.t\n")
            elif fin_flag[1] == "l"  and fin_flag[2] == "=":
               fout.write ("  type l = String.t\n")
            elif fin_flag[1] == "align"  and fin_flag[2] == "=":
              fout.write ("  type align = int\n")
            elif fin_flag[1] == "sz"  and fin_flag[2] == "=":
              fout.write ("  type sz = int\n")
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

# main 

read_file()
