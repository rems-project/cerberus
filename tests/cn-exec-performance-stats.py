#!/usr/bin/env python3

import subprocess
from os import listdir
from os.path import isfile, join
import argparse, sys, os
import pandas as pd
import numpy as np




parser=argparse.ArgumentParser()

parser.add_argument("--dir", help="Collect performance metrics for *directory* of CN files")
parser.add_argument("--file", help="Collect performance metrics for a *single* CN file")
parser.add_argument("--csv", help="Store all results in csv file with provided name")
parser.add_argument("--csv_clean", help="Store most useful results in csv file with provided name")
parser.add_argument("--iterate", help="Iterate up to 2**(n-1)")
parser.add_argument("--buddy_path", help="Collect statistics for pKVM buddy allocator - provide path to buddy")
parser.add_argument("--preprocess", action='store_true', help='Preprocess input file before generating executable')
parser.add_argument("--track_owned", action='store_true', help='Track number of Owned predicates dynamically')
parser.set_defaults(preprocess=False)
parser.set_defaults(track_owned=False)

args=parser.parse_args()

if (not (args.dir or args.file or args.buddy_path)):
    print("Please provide an argument for --dir, --file or --buddy_path")
    exit()

if args.csv:
    if ".csv" not in args.csv:
        print("Please provide CSV file extension explicitly in --csv arg")
        exit()

if args.csv_clean:
    if ".csv" not in args.csv_clean:
        print("Please provide CSV file extension explicitly in --csv_clean arg")
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
    tests_path = args.buddy_path
    cn_test_files=["driver-pp.c"]

# print(cn_test_files)
time_cmd_str = 'gtime -f ~%e~%M '


generation_times=[]
compilation_times={'instrumented': [], 'uninstrumented': []}
link_times={'instrumented': [], 'uninstrumented': []}
executable_times={'instrumented': [], 'uninstrumented': []}
nr_owned_predicates=[]
generation_space=[]
compilation_space={'instrumented': [], 'uninstrumented': []}
link_space={'instrumented': [], 'uninstrumented': []}
executable_space={'instrumented': [], 'uninstrumented': []}

non_error_cn_filenames=[]

opam_switch_prefix = os.environ["OPAM_SWITCH_PREFIX"]
runtime_prefix = opam_switch_prefix + "/lib/cn/runtime"

num_error_files=0

def print_and_error(error_str):
    # global num_error_files
    print(error_str + " ERROR")
    exit()
    # num_error_files+=1


def gen_instr_cmd(f, input_basename):
    instr_cmd_prefix = "cn instrument"
    instr_cmd = time_cmd_str + instr_cmd_prefix + " " + tests_path + "/" + f
    instr_cmd += " --output-decorated=" + input_basename + "-exec.c"
    return instr_cmd

def gen_compile_cmd(input_basename, instrumented):
    c_files = input_basename + "-exec.c cn.c" if instrumented else tests_path + "/" + input_basename + ".c "
    if not instrumented:
        c_files += "cn_uninstr_defs.c"
    compile_cmd = time_cmd_str + "cc "
    if not instrumented:
        compile_cmd += "-I " + "cn_uninstr_defs.h "
    compile_cmd += "-g -c "
    if instrumented:
        compile_cmd += "-I" + runtime_prefix + "/include/ "
    compile_cmd += c_files
    return compile_cmd

def gen_link_cmd(input_basename, instrumented):
    o_files = input_basename + "-exec.o cn.o " if instrumented else input_basename + ".o "
    if not instrumented:
        o_files += " cn_uninstr_defs.o "
    bin_file = input_basename + "-exec-output.bin " if instrumented else input_basename + "-output.bin "
    link_cmd = time_cmd_str + "cc "
    if instrumented:
        link_cmd += "-I" + runtime_prefix + "/include "
    if not instrumented:
        link_cmd += "-I " + "cn_uninstr_defs.h "
    link_cmd += "-o " + bin_file + o_files
    if instrumented:
        link_cmd += runtime_prefix + "/libcn.a"
    return link_cmd

def gen_exec_cmd(input_basename, instrumented):
    bin_file = input_basename + "-exec-output.bin " if instrumented else input_basename + "-output.bin"
    exec_cmd = time_cmd_str + "./" + bin_file
    return exec_cmd

def time_cmd(cmd, error_msg, executable=False):
    res = subprocess.run(cmd.split(), capture_output=True, text = True)
    output = res.stderr
    success_flag = not res.returncode
    cmd_stats = {}
    if success_flag:
        # print(instr_output)
        collected_stats = output.split('~')[-2:]
        cmd_stats['time'] = collected_stats[0]
        cmd_stats['space'] = collected_stats[1]
        if executable and args.track_owned:
            owned_stats = res.stdout.split('£')[-1]
            cmd_stats['nr_owned_predicates'] = owned_stats
        # print(generation_time)
    else:
        if executable:
            print("Stdout:")
            print(res.stdout)
            print("Stderr:")
            print(output)
        print_and_error(error_msg)
    return success_flag, cmd_stats


def time_spec_generation(f, input_basename):
    instr_cmd = gen_instr_cmd(f, input_basename)
    print(instr_cmd)
    return time_cmd(instr_cmd, "GENERATION")


def time_compilation(input_basename, instrumented):
    compile_cmd = gen_compile_cmd(input_basename, instrumented)
    print(compile_cmd)
    return time_cmd(compile_cmd, "COMPILATION")


        
def time_linking(input_basename, instrumented):
    link_cmd = gen_link_cmd(input_basename, instrumented)
    print(link_cmd)
    return time_cmd(link_cmd, "LINKING")


def time_executable(input_basename, instrumented):
    executable_cmd = gen_exec_cmd(input_basename, instrumented)
    print(executable_cmd)
    return time_cmd(executable_cmd, "EXECUTABLE", executable=True)


def preprocess_file(filename, input_basename):
    preprocess_cmd = "cc -E -P -CC " + tests_path + "/" + filename
    print(preprocess_cmd)
    pp_f_name = input_basename + "-pp.c"
    pp_f = open(tests_path + "/" + pp_f_name, "w")
    subprocess.call(preprocess_cmd.split(), stdout=pp_f)
    return pp_f_name

def find_and_replace_macro(f, input_basename, str_being_replaced, new_str):
    # Assume there is a macro of the form #define SIZE magic in the input file
    with open(tests_path + "/" + f, 'r') as file:
        filedata = file.read()

    filedata = filedata.replace(str_being_replaced, new_str)
    subst_f_name = input_basename + "-subst.c"

    with open(tests_path + "/" + subst_f_name, 'w') as file:
        file.write(filedata)

    return subst_f_name

def run_cmds_and_collect_stats(f, input_basename, instrumented):
    single_run_stats_dict = {}
    # Instrumented run
    generation_successful = True
    if instrumented:
        generation_successful, generation_stats = time_spec_generation(f, input_basename)

    if generation_successful:
        compilation_successful, compilation_stats = time_compilation(input_basename, instrumented)

        if compilation_successful:
            linking_successful, link_stats = time_linking(input_basename, instrumented)

            if linking_successful:
                executable_successful, executable_stats = time_executable(input_basename, instrumented)
                if instrumented:
                    single_run_stats_dict["generation"] = generation_stats

                single_run_stats_dict["compilation"] = compilation_stats
                single_run_stats_dict["linking"] = link_stats
                single_run_stats_dict["executable"] = executable_stats
                return executable_successful, single_run_stats_dict

    return False, {}


def collect_stats_for_single_file(f, input_basename):
    # Uninstrumented run
    uninstr_executable_successful, uninstr_stats_dict = run_cmds_and_collect_stats(f, input_basename, instrumented=False)

    # Instrumented run
    instr_executable_successful, instr_stats_dict = run_cmds_and_collect_stats(f, input_basename, instrumented=True)
    if instr_executable_successful and uninstr_executable_successful:
        # Instrumented stats
        generation_times.append(float(instr_stats_dict["generation"]['time']))
        compilation_times['instrumented'].append(float(instr_stats_dict["compilation"]['time']))
        link_times['instrumented'].append(float(instr_stats_dict["linking"]['time']))
        executable_times['instrumented'].append(float(instr_stats_dict["executable"]['time']))
        generation_space.append(float(instr_stats_dict["generation"]['space']))
        compilation_space['instrumented'].append(float(instr_stats_dict["compilation"]['space']))
        link_space['instrumented'].append(float(instr_stats_dict["linking"]['space']))
        executable_space['instrumented'].append(float(instr_stats_dict["executable"]['space']))
        if args.track_owned:
            nr_owned_predicates.append(float(instr_stats_dict["executable"]['nr_owned_predicates']))

        # Uninstrumented stats
        compilation_times['uninstrumented'].append(float(uninstr_stats_dict["compilation"]['time']))
        link_times['uninstrumented'].append(float(uninstr_stats_dict["linking"]['time']))
        executable_times['uninstrumented'].append(float(uninstr_stats_dict["executable"]['time']))
        compilation_space['uninstrumented'].append(float(uninstr_stats_dict["compilation"]['space']))
        link_space['uninstrumented'].append(float(uninstr_stats_dict["linking"]['space']))
        executable_space['uninstrumented'].append(float(uninstr_stats_dict["executable"]['space']))

        non_error_cn_filenames.append(f)

print("Collecting performance metrics...")

if args.buddy_path and not args.iterate:
    preprocess_file("driver.c", "driver")


num_elements_list=[]

for f in cn_test_files:
    input_basename = f.split('.')[0]
    if args.iterate:
        for i in range(1, int(args.iterate)):
            num_elements = 2**i
            print(f)
            subst_f = find_and_replace_macro(f, input_basename, "magic", str(num_elements))
            pp_f = preprocess_file(subst_f, input_basename + "-subst")
            collect_stats_for_single_file(pp_f, input_basename + "-subst-pp")
            num_elements_list.append(num_elements)
    else:
        collect_stats_for_single_file(f, input_basename)



print("...done!")

stats_dict = {'cn_filename': non_error_cn_filenames}

if args.iterate:
    stats_dict['num_elements'] = num_elements_list

stats_dict['instr_generation_time'] = generation_times
stats_dict['instr_compilation_time'] = compilation_times['instrumented']
stats_dict['instr_linking_time'] = link_times['instrumented']
stats_dict['instr_executable_time'] = executable_times['instrumented']

stats_dict['instr_generation_space'] = generation_space
stats_dict['instr_compilation_space'] = compilation_space['instrumented']
stats_dict['instr_linking_space'] = link_space['instrumented']
stats_dict['instr_executable_space'] = executable_space['instrumented']
if args.track_owned:
    stats_dict['nr_owned_predicates'] = nr_owned_predicates

stats_dict['uninstr_compilation_time'] = compilation_times['uninstrumented']
stats_dict['uninstr_linking_time'] = link_times['uninstrumented']
stats_dict['uninstr_executable_time'] = executable_times['uninstrumented']

stats_dict['uninstr_compilation_space'] = compilation_space['uninstrumented']
stats_dict['uninstr_linking_space'] = link_space['uninstrumented']
stats_dict['uninstr_executable_space'] = executable_space['uninstrumented']

full_df = pd.DataFrame.from_dict(stats_dict)

# Total time and space
full_df["instr_total_time"] = full_df[['instr_generation_time', 'instr_compilation_time', 'instr_linking_time', 'instr_executable_time']].sum(axis=1)
full_df["instr_total_space"] = full_df[['instr_generation_space', 'instr_compilation_space', 'instr_linking_space', 'instr_executable_space']].sum(axis=1)
full_df["uninstr_total_time"] = full_df[['uninstr_compilation_time', 'uninstr_linking_time', 'uninstr_executable_time']].sum(axis=1)
full_df["uninstr_total_space"] = full_df[['uninstr_compilation_space', 'uninstr_linking_space', 'uninstr_executable_space']].sum(axis=1)

# Differences in executable time and space
full_df["executable_time_difference"] = full_df['instr_executable_time'] - full_df['uninstr_executable_time']
full_df["executable_space_difference"] = full_df['instr_executable_space'] - full_df['uninstr_executable_space']

print(full_df)

if args.csv:
    full_df.to_csv(args.csv, index=False) 

if args.csv_clean:
    if args.iterate:
        copied_cols = ['cn_filename', 'num_elements']
        if args.track_owned:
            copied_cols += ['nr_owned_predicates']
        copied_cols += ['uninstr_executable_time', 'uninstr_executable_space', 'executable_time_difference', 'executable_space_difference']
        iterated_clean_df = full_df[copied_cols].copy()
        iterated_clean_df['log2_executable_time_difference'] = np.log2(abs(iterated_clean_df['executable_time_difference']))
        iterated_clean_df['log2_executable_space_difference'] = np.log2(abs(iterated_clean_df['executable_space_difference']))
        iterated_clean_df.to_csv(args.csv_clean, index=False) 
    else:
        clean_stats_dict = {
            'mean_generation_time': [full_df.loc[:, 'instr_generation_time'].mean()],
            'std_generation_time': [full_df['instr_generation_time'].std()],
            'mean_uninstr_exec_time': [full_df.loc[:, 'uninstr_executable_time'].mean()],
            'std_uninstr_exec_time': [full_df['uninstr_executable_time'].std()],
            'mean_uninstr_exec_space': [full_df.loc[:, 'uninstr_executable_space'].mean()],
            'std_uninstr_exec_space': [full_df['uninstr_executable_space'].std()],
            'mean_exec_time_difference': [full_df.loc[:, 'executable_time_difference'].mean()],
            'std_exec_time_difference': [full_df['executable_time_difference'].std()],
            'mean_exec_space_difference': [full_df.loc[:, 'executable_space_difference'].mean()],
            'std_exec_space_difference': [full_df['executable_space_difference'].std()], 
        }

        clean_df = pd.DataFrame.from_dict(clean_stats_dict)
        clean_df.to_csv(args.csv_clean, index=False) 



print("Number of error files:")
print(num_error_files)
