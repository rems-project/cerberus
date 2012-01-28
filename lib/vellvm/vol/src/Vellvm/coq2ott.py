#! /usr/bin/env python

import sys, string, os, commands, shutil, re
from math import sqrt, log10, log
from operator import itemgetter

def read_file():
  fott=open("infrastructure.ott", 'r')
  fcoq=open("infrastructure_aux.v", 'r')
  fmerge=open("merge.ott", 'w')

  from_ott = True
  from_coq = False

  for ott_buffer in fott:
    ott_flag = string.split(ott_buffer)
    if len(ott_flag) > 0 :
      if ott_flag[0] == "(*BEGINCOPY*)":
        from_ott = False
      if ott_flag[0] == "(*ENDCOPY*)":
        from_ott = True
    if from_ott == True:
      fmerge.write (ott_buffer)
    else:
      for coq_buffer in fcoq:
        coq_flag = string.split(coq_buffer)
        if len(coq_flag) > 0 :
          if coq_flag[0] == "(*BEGINCOPY*)":
            from_coq = True
          if coq_flag[0] == "(*ENDCOPY*)":
            from_coq = False
        if from_coq == True:
          fmerge.write (coq_buffer)
        
  fott.close()
  fcoq.close()
  fmerge.close()

# main 

read_file()
