#!/usr/bin/env python3

import subprocess
from os import listdir
from os.path import isfile, join
import argparse, sys, os
import pandas as pd




parser=argparse.ArgumentParser()

parser.add_argument("--dir", help="Collect performance metrics for *directory* of CN files")
parser.add_argument("--file", help="Collect performance metrics for a *single* CN file")
parser.add_argument("--csv", help="Store results in csv file with provided name")

args=parser.parse_args()

if (not args.dir and not args.file) or (args.dir and args.file):
    print("Please provide *either* a standalone CN file *or* a directory path for several CN files")
    exit()

if ".csv" not in args.csv:
    print("Please provide CSV file extension explicitly in --csv arg")
    exit()


cn_test_files=[]
tests_path=""
if args.dir:
    tests_path = args.dir
    cn_test_files = [f for f in listdir(tests_path) if (isfile(join(tests_path, f)) and ".broken" not in f and ".c" in f)]
else:
    filename_split = args.file.split('/')
    tests_path = '/'.join(filename_split[:-1])
    cn_test_files=[filename_split[-1]]

# print(cn_test_files)
time_cmd = "time "

generation_times=[]
compilation_times=[]
link_times=[]
executable_times=[]

non_error_cn_filenames=[]

opam_switch_prefix = os.environ["OPAM_SWITCH_PREFIX"]
runtime_prefix = opam_switch_prefix + "/lib/cn/runtime"

num_error_files=0

def print_and_error():
    global num_error_files
    print("ERROR")
    num_error_files+=1

def time_spec_generation(f, input_basename):
    instr_cmd_prefix = "cn instrument"
    instr_cmd = time_cmd + instr_cmd_prefix + " " + tests_path + "/" + f
    instr_cmd += " --output-decorated=" + input_basename + "-exec.c"
    instr_cmd += " --with-ownership-checking"
    instr_result = subprocess.run(instr_cmd.split(), capture_output=True, text = True)
    instr_output = instr_result.stderr
    successful_gen_flag = "error" not in instr_output
    generation_time = None
    if successful_gen_flag:
        generation_time = instr_output.split()[0]
        # print(generation_time)
    else:
        print_and_error()
    return successful_gen_flag, generation_time


def time_compilation(input_basename):
    compile_cmd = time_cmd + "cc -g -c -I" + runtime_prefix + "/include/ " + input_basename + "-exec.c cn.c"
    compile_result = subprocess.run(compile_cmd.split(), capture_output=True, text = True)
    compile_output = compile_result.stderr
    successful_compile_flag = "error" not in compile_output
    compilation_time = None
    if successful_compile_flag:
        compilation_time = compile_output.split()[0]
    else:
        print_and_error()
    return successful_compile_flag, compilation_time
        
def time_linking(input_basename):
    link_cmd = time_cmd + "cc -I" + runtime_prefix + "/include -o " + input_basename + "-exec-output.bin " + input_basename + "-exec.o cn.o " + runtime_prefix + "/libcn.a"
    link_result = subprocess.run(link_cmd.split(), capture_output=True, text = True)
    link_output = link_result.stderr
    successful_linking_flag = "error" not in link_output
    link_time = None
    if successful_linking_flag:
        link_time = link_output.split()[0]
    else:
        print_and_error()
    return successful_linking_flag, link_time

def time_executable(input_basename):
    executable_cmd = time_cmd + "./" + input_basename + "-exec-output.bin"
    executable_result = subprocess.run(executable_cmd.split(), capture_output=True, text = True)
    executable_output = executable_result.stderr
    successful_executable_flag = "error" not in executable_output
    executable_time = None
    if successful_executable_flag:
        executable_time = executable_output.split()[0]
    else:
        print_and_error()
    return successful_executable_flag, executable_time


print("Collecting performance metrics...")

for f in cn_test_files:
    print(f)
    # Generation
    input_basename = f.split('.')[0]
    generation_successful, generation_time = time_spec_generation(f, input_basename)
    if generation_successful:
        # print("Generation successful")
        # Compilation
        print(input_basename)
        compilation_successful, compilation_time = time_compilation(input_basename)
        if compilation_successful:
            # print("Compilation successful")
            # Linking
            linking_successful, link_time = time_linking(input_basename)
            if linking_successful:
                # print("Linking successful")
                # Running binary
                executable_successful, executable_time = time_executable(input_basename)
                if executable_successful:
                    # print("Executable ran successfully")
                    generation_times.append(float(generation_time))
                    compilation_times.append(float(compilation_time))
                    link_times.append(float(link_time))
                    executable_times.append(float(executable_time))
                    non_error_cn_filenames.append(f)



print("...done!")

stats_dict = \
{'cn_filename': non_error_cn_filenames,
 'generation_time': generation_times, 
 'compilation_time': compilation_times,
 'linking_time': link_times,
 'executable_time': executable_times}

df = pd.DataFrame.from_dict(stats_dict)
df["total"] = df.iloc[:, -4:].sum(axis=1)

print(df)

if args.csv:
    df.to_csv(args.csv, index=False) 

print("Number of error files:")
print(num_error_files)
