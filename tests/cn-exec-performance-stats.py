#!/usr/bin/env python3

import subprocess
from os import listdir
from os.path import isfile, join
import sys
import pandas as pd

if len(sys.argv) != 2:
    print("Please provide directory of CN files")
    exit()

tests_path = sys.argv[1]
cn_test_files = [f for f in listdir(tests_path) if (isfile(join(tests_path, f)) and ".error" not in f)]

# print(cn_test_files)
instr_cmd_prefix = "time cn instrument"
num_error_files=0

generation_times=[]

for f in cn_test_files:
    print(tests_path + "/" + f)
    full_instr_cmd = instr_cmd_prefix + " " + tests_path + "/" + f
    result = subprocess.run(full_instr_cmd.split(), capture_output=True, text = True)
    output = result.stderr
    if "error" not in output:
        generation_time = output.split()[0]
        print(generation_time)
        generation_times.append(generation_time)
    else:
        print("ERROR")
        num_error_files+=1

stats_dict = {'generation_time': generation_times}
df = pd.DataFrame.from_dict(stats_dict)

print(df)

print("Number of error files:")
print(num_error_files)
