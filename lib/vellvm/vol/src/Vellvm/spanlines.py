#! /usr/bin/env python

import sys, string, os, commands, shutil, re
from math import sqrt, log10, log
from operator import itemgetter

def read_file(input, output):
  fott=open(input, 'r')
  fmott=open(output, 'w')

  spanlines = False
  linenums = 0

  for ott_buffer in fott:
    ott_flag = string.split(ott_buffer)
    if len(ott_flag) > 0 :
      if ott_flag[0] == "<<":
        spanlines = True
        fmott.write ("%<<\n")
        continue
      if ott_flag[0] == ">>":
        spanlines = False
        fmott.write ("\n")
        for i in range(linenums-1):
          fmott.write ("%\n")
        fmott.write ("%>>\n")
        continue
    if spanlines == False:
      fmott.write (ott_buffer)
    else:
      linenums = linenums + 1
      fmott.write (string.replace(ott_buffer, "\n", " "))
        
  fott.close()
  fmott.close()

# main 

read_file(sys.argv[1], "m_"+sys.argv[1])
