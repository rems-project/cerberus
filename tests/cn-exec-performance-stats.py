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
parser.add_argument("--iterate", action='store_true', help="Iterate over various sizes of data structure")
parser.add_argument("--buddy_path", help="Collect statistics for pKVM buddy allocator - provide path to buddy")
parser.add_argument("--preprocess", action='store_true', help='Preprocess input file before generating executable')
parser.set_defaults(iterate=False)
parser.set_defaults(preprocess=False)

args=parser.parse_args()

if (not (args.dir or args.file or args.buddy_path)):
    print("Please provide an argument for --dir, --file or --buddy_path")
    exit()

if ".csv" not in args.csv:
    print("Please provide CSV file extension explicitly in --csv arg")
    exit()


cn_test_files=[]
tests_path=""
if args.dir:
    tests_path = args.dir
    cn_test_files = [f for f in listdir(tests_path) if (isfile(join(tests_path, f)) and ".broken" not in f and ".c" in f)]
elif args.file:
    filename_split = args.file.split('/')
    tests_path = '/'.join(filename_split[:-1])
    cn_test_files=[filename_split[-1]]
elif args.buddy_path:
    tests_path = "."
    cn_test_files=["driver.pp.c"]

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

def print_and_error(error_str):
    global num_error_files
    print(error_str + " ERROR")
    num_error_files+=1

def gen_instr_cmd(f, input_basename):
    instr_cmd_prefix = "cn instrument"
    instr_cmd = time_cmd + instr_cmd_prefix + " " + tests_path + "/" + f
    instr_cmd += " --output-decorated=" + input_basename + "-exec.c"
    instr_cmd += " --with-ownership-checking"
    return instr_cmd

def gen_compile_cmd(input_basename):
    compile_cmd = time_cmd + "cc -g -c -I" + runtime_prefix + "/include/ " + input_basename + "-exec.c cn.c"
    return compile_cmd

def gen_link_cmd(input_basename):
    link_cmd = time_cmd + "cc -I" + runtime_prefix + "/include -o " + input_basename + "-exec-output.bin " + input_basename + "-exec.o cn.o " + runtime_prefix + "/libcn.a"
    return link_cmd

def gen_exec_cmd(input_basename):
    exec_cmd = time_cmd + "./" + input_basename + "-exec-output.bin"
    return exec_cmd

def is_non_error_output(output):
    return ("error" not in output) or ("Out of memory!" not in output) or args.buddy_path

def time_spec_generation(f, input_basename):
    instr_cmd = gen_instr_cmd(f, input_basename)
    print(instr_cmd)
    instr_result = subprocess.run(instr_cmd.split(), capture_output=True, text = True)
    instr_output = instr_result.stderr
    successful_gen_flag = is_non_error_output(instr_output)
    generation_time = None
    if successful_gen_flag:
        generation_time = instr_output.split()[-6:][0]
        # print(generation_time)
    else:
        print_and_error("GENERATION")
    return successful_gen_flag, generation_time


def time_compilation(input_basename):
    compile_cmd = gen_compile_cmd(input_basename)
    print(compile_cmd)
    compile_result = subprocess.run(compile_cmd.split(), capture_output=True, text = True)
    compile_output = compile_result.stderr
    successful_compile_flag = is_non_error_output(compile_output)
    compilation_time = None
    if successful_compile_flag:
        compilation_time = compile_output.split()[-6:][0]
    else:
        print_and_error("COMPILATION")
    return successful_compile_flag, compilation_time

        
def time_linking(input_basename):
    link_cmd = gen_link_cmd(input_basename)
    print(link_cmd)
    link_result = subprocess.run(link_cmd.split(), capture_output=True, text = True)
    link_output = link_result.stderr
    successful_linking_flag = is_non_error_output(link_output)
    link_time = None
    if successful_linking_flag:
        link_time = link_output.split()[-6:][0]
    else:
        print_and_error("LINKING")
    return successful_linking_flag, link_time

def time_executable(input_basename, c_arg):
    executable_cmd = gen_exec_cmd(input_basename)
    if c_arg:
        executable_cmd += " " + str(c_arg)
    print(executable_cmd)
    executable_result = subprocess.run(executable_cmd.split(), capture_output=True, text = True)
    executable_output = executable_result.stderr
    successful_executable_flag = is_non_error_output(executable_output)
    executable_time = None
    if successful_executable_flag:
        executable_time = executable_output.split()[-6:][0]
    else:
        print_and_error("EXECUTABLE")
    return successful_executable_flag, executable_time

def preprocess_buddy():
    preprocess_cmd = "cc -E -P -CC " + args.buddy_path + "driver.c"
    print(preprocess_cmd)
    pp_f = open("driver.pp.c", "w")
    subprocess.call(preprocess_cmd.split(), stdout=pp_f)



def collect_stats_for_single_file(f, c_arg=None):
    # print(f)
    # Generation
    
    input_basename = f.split('.')[0]
    generation_successful, generation_time = time_spec_generation(f, input_basename)
    if generation_successful:
        # print("Generation successful")
        # Compilation
        # print(input_basename)
        compilation_successful, compilation_time = time_compilation(input_basename)
        if compilation_successful:
            # print("Compilation successful")
            # Linking
            linking_successful, link_time = time_linking(input_basename)
            if linking_successful:
                # print("Linking successful")
                # Running binary
                executable_successful, executable_time = time_executable(input_basename, c_arg)
                if executable_successful:
                    # print("Executable ran successfully")
                    generation_times.append(float(generation_time))
                    compilation_times.append(float(compilation_time))
                    link_times.append(float(link_time))
                    executable_times.append(float(executable_time))
                    non_error_cn_filenames.append(f)
    

print("Collecting performance metrics...")

if args.buddy_path:
    preprocess()


num_elements_list=[]

for f in cn_test_files:
    if args.iterate:
        for i in range(200):
            num_elements = 2**i
            collect_stats_for_single_file(f, num_elements)
            num_elements_list.append(num_elements)
    else:
        collect_stats_for_single_file(f)



print("...done!")

stats_dict = {'cn_filename': non_error_cn_filenames}

if args.iterate:
    stats_dict['num_elements'] = num_elements_list

stats_dict['generation_time'] = generation_times
stats_dict['compilation_time'] = compilation_times
stats_dict['linking_time'] = link_times
stats_dict['executable_time'] = executable_times

df = pd.DataFrame.from_dict(stats_dict)
df["total"] = df.iloc[:, -4:].sum(axis=1)

print(df)

if args.csv:
    df.to_csv(args.csv, index=False) 

print("Number of error files:")
print(num_error_files)
