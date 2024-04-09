#!/usr/bin/python

# run instances with list by base solver

import os
import sys
import time
import random
import datetime
import subprocess
import multiprocessing

import ListJobCollector

# fixed
input_dir_path_template      = r'benchmarks/{}'
base_solver_path_template    = r'bin/linux-prebuilt/base-solvers/{}'
output_dir_pre_path_template = r'AE-test-output/{}/raw-results/{}/{}-p1'

def make_dir(dir):
    os.system('mkdir -p ' + dir)

def make_prefix_dirs(jobs_list: list):
    vis_dict = {}
    for job in jobs_list:
        pre_path : str = output_dir_pre_path + job[ : job.rfind('/')]
        if not vis_dict.get(pre_path, False):
            vis_dict[pre_path] = True
            make_dir(pre_path)
            
def solve(job : str, cnt : int):
    input_path = input_dir_path + job
    output_path = output_dir_pre_path + job
    start_time = time.time()
    try:
        cmd = " ".join(["ulimit", "-S", "-t", f'{time_limit:.0f}'] \
                        + [";"] + [base_solver_path, input_path])
        result = subprocess.run(cmd,
                                shell=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE
                            )
    except subprocess.CalledProcessError as e:
        pass
    else:
        pass
    end_time = time.time()

    result_lines = result.stdout.decode("utf-8").split("\n")
    state : str = result_lines[0]
    cost_time = end_time - start_time
    if state not in ['sat', 'unsat']:
        state = 'failed'
        cost_time = time_limit
    with open(output_path, mode="w") as of:
        of.write(f"{state}\n{cost_time}\n")

    return job, cnt, state, cost_time

def get_current_infos(not_done = True):
    curr_time = time.time()
    cost_time = curr_time - start_time
    estimated_time = cost_time / processed_job * total_job
    left_time = estimated_time - cost_time

    ret = ''
    if not_done:
        ret += ' ++++++ show progress ++++++ ' + '\n'
    ret += 'start time: ' + time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(start_time)) + '\n'
    ret += 'current time: ' + time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(curr_time)) + '\n'
    ret += 'cost time: ' + str(datetime.timedelta(seconds=cost_time)) + '\n'
    if not_done:
        ret += 'left time: ' + str(datetime.timedelta(seconds=left_time)) + '\n'
        ret += 'estimated time: ' + str(datetime.timedelta(seconds=estimated_time)) + '\n'
        ret += 'estimated finished time: ' + time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(start_time + estimated_time)) + '\n'
    ret += 'instance per seconed(all process): {:.2f}'.format(processed_job / cost_time) + '\n'
    ret += 'instance average runtime(s): {:.2f}'.format(cost_time * max_process_num / processed_job) + '\n'
    if not_done:
        ret += 'finished persent: {:.2f}%'.format(processed_job / total_job * 100.0) + '\n'
    ret += 'processed jobs: {}'.format(processed_job) + '\n'
    
    unprocessed_job = total_job - processed_job
    
    ret += 'unprocessed jobs: {}'.format(unprocessed_job) + '\n'
    ret += 'unsolved jobs: {}'.format(unsolved_job) + '\n'
    ret += 'solved jobs: {}'.format(solved_job) + '\n'
    ret += 'sat jobs: {}'.format(sat_job) + '\n'
    ret += 'unsat jobs: {}'.format(unsat_job) + '\n'
    if not_done:
        if unprocessed_job > max_process_num:
            estimated_unsolved = (unsolved_job + max_process_num) / (processed_job + max_process_num) * total_job
        else:
            estimated_unsolved = unsolved_job + unprocessed_job
        estimated_solved = total_job - estimated_unsolved
        ret += 'estimated solved: {:.2f}'.format(estimated_solved) + '\n'
        ret += 'estimated unsolved: {:.2f}'.format(estimated_unsolved) + '\n'
        ret += ' ------ show progress ------ ' + '\n'
    return ret

def process_callback(result):
    # global processed_job
    # global solved_job
    global processed_job
    global solved_job
    global unsolved_job
    global sat_job
    global unsat_job
    global start_time
    job, cnt, state, job_cost_time = result
    
    curr_time = time.time()
    cost_time = curr_time - start_time
    
    if state in ['sat', 'unsat']:
        solved_job += 1
        if state == 'sat':
            sat_job += 1
        elif state == 'unsat':
            unsat_job += 1
        with open(f'{output_dir_pre_path}/solved_list.txt', mode='a') as f:
            f.write(f'{job}\n')
            f.write(f'[{str(datetime.timedelta(seconds=cost_time))}] solved state: {state}, cost time: {job_cost_time:.2f}\n')
    else:
        unsolved_job += 1
        with open(f'{output_dir_pre_path}/unsolved_list.txt', mode='a') as f:
            f.write(f'{job}\n')
            f.write(f'[{str(datetime.timedelta(seconds=cost_time))}] unsolved state: {state}\n')
        
    processed_job += 1

    info = '{}/{}: finish job file[{}] = {}, state: {}' \
            .format(processed_job, len(jobs_list), cnt, job, state)
    print(info)
    if processed_job % 10 == 0:
        print(get_current_infos())
    
    sys.stdout.flush()
    
def process_error(error):
    print(f'error: {error}')

def init_counters():
    global processed_job
    global solved_job
    global unsolved_job
    global sat_job
    global unsat_job
    processed_job = 0
    solved_job = 0
    unsolved_job = 0
    sat_job = 0
    unsat_job = 0

def RIWL_BaseSolver(_max_process_num: int, _benchmark_tag: str,
                  _list_tag: str, _base_solver_tag: str, 
                  _test_type: str, _lists_dir_path: str, _time_limit: float):
    
    init_counters()
    
    global max_process_num
    global list_tag
    global base_solver_tag
    global test_type
    global instance_list_path
    global time_limit
    
    max_process_num  = _max_process_num
    list_tag = _list_tag
    base_solver_tag = _base_solver_tag
    test_type = _test_type
    instance_list_path  = f'{_lists_dir_path}/{_list_tag}.txt'
    time_limit = _time_limit
        
    global input_dir_path
    global base_solver_path
    global output_dir_pre_path
    
    input_dir_path = input_dir_path_template.format(_benchmark_tag)
    base_solver_path = base_solver_path_template.format(base_solver_tag)
    output_dir_pre_path = output_dir_pre_path_template.format(test_type, list_tag, base_solver_tag)
    
    global jobs_list
    global start_time
    global total_job
    
    jobs_list = ListJobCollector.CollectListJobs(instance_list_path)
    total_job = len(jobs_list)
    
    if os.path.exists(output_dir_pre_path):
        os.system(f'rm -r {output_dir_pre_path}')
    
    start_time = time.time()
    
    make_dir(output_dir_pre_path)
    make_prefix_dirs(jobs_list)
    
    with open(f'{output_dir_pre_path}/solved_list.txt', mode='w') as f:
        f.write('solved list:\n')
    with open(f'{output_dir_pre_path}/unsolved_list.txt', mode='w') as f:
        f.write('unsolved list:\n')
    
    with multiprocessing.Pool(processes=max_process_num) as pool:
        cnt = 0
        rng = random.Random(0)
        random.shuffle(jobs_list, rng.random)
        for job in jobs_list:
            res = pool.apply_async(solve, (job, cnt, ), callback=process_callback, error_callback=process_error)
            cnt = cnt + 1  
        print('# all tasks are assigned')
        pool.close()
        pool.join()
        print('# all problems are processed')
    
    infos = get_current_infos(False)
    print(f'theory: {list_tag}')
    print(infos)
    with open(output_dir_pre_path + '/sumup.txt', 'w') as f:
        f.write(infos)

if __name__ == '__main__':
    
    # parameter
    # list_tag = r'QF_NRA-12134'
    # list_tag = r'QF_NIA-25358'
    # list_tag = r'QF_LIA-13226'
    # list_tag = r'QF_LRA-1753'

    # base_solver_tag = r'cvc5-1.0.8'
    # base_solver_tag = r'z3-4.12.1'
    # base_solver_tag = r'opensmt-2.5.2'

    # test_type = 'all'
    # instance_list_path = 'benchmark-lists/all/QF_LRA-all_list-1753.txt'
    
    RIWL_BaseSolver(1, 'QF_LRA-1753', 'QF_LRA-1753', 'cvc5-1.0.8', 'all', 'benchmark-lists/all', 60)
    
'''

'''
    