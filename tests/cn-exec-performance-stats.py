#!/usr/bin/env python3

import subprocess
from os import listdir
from os.path import isfile, join
import argparse, sys
import pandas as pd

parser=argparse.ArgumentParser()

parser.add_argument("--dir", help="Collect performance metrics for *directory* of CN files")
parser.add_argument("--file", help="Collect performance metrics for a *single* CN file")

args=parser.parse_args()

if (not args.dir and not args.file) or (args.dir and args.file):
    print("Please provide *either* a standalone CN file *or* a directory path for several CN files")
    exit()


cn_test_files=[]
tests_path=""
if args.dir:
    tests_path = args.dir
    cn_test_files = [f for f in listdir(tests_path) if (isfile(join(tests_path, f)) and ".broken" not in f and ".c" in f)]
else:
    cn_test_files=[args.file]

# print(cn_test_files)
instr_cmd_prefix = "time cn instrument"
num_error_files=0

generation_times=[]
non_error_cn_filenames=[]

print("Collecting performance metrics...")

for f in cn_test_files:
    # print(tests_path + "/" + f)
    full_instr_cmd = instr_cmd_prefix + " " + tests_path + "/" + f
    result = subprocess.run(full_instr_cmd.split(), capture_output=True, text = True)
    output = result.stderr
    if "error" not in output:
        generation_time = output.split()[0]
        # print(generation_time)
        generation_times.append(generation_time)
        non_error_cn_filenames.append(f)
    else:
        print("ERROR")
        num_error_files+=1

print("...done!")

stats_dict = {'cn_filename': non_error_cn_filenames, 'generation_time': generation_times}
df = pd.DataFrame.from_dict(stats_dict)

print(df)
df.to_csv('times.csv', index=False) 

print("Number of error files:")
print(num_error_files)
