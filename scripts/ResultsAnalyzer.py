#!/usr/bin/python
import os
import ResultsProcesser
import ListJobCollector
from tabulate import tabulate

base_solver_tags = [
    'cvc5-1.0.8',
    'opensmt-2.5.2',
    'z3-4.12.1',
]

def sumup_result(job_list, res):
    ret = {
            'sat': 0,
            'unsat': 0,
            'solved': 0,
            'failed': 0,
            'PAR-2': 0.0, 
        }
    for i in range(len(job_list)):
        ret[res[i][0]] += 1
        if res[i][0] in ['sat', 'unsat']:
            ret['solved'] += 1
            ret['PAR-2'] += float(res[i][1])
        else:
            ret['PAR-2'] += 2 * time_limit
    return ret

def count_results(tag: str, job_list, tag_result):
    sumupInfo = sumup_result(job_list, tag_result)
    sumupInfo['PAR-2'] = int(sumupInfo['PAR-2'])
    return sumupInfo
    
def process_theory(theory_tag: str, list_tag: str):
    
    print(f'analyze theory: {theory_tag}')
    job_list = ListJobCollector.CollectListJobs(instance_list_path)
    sumups = [['solver', 'sat', 'unsat', 'solved', 'failed', 'PAR-2']]
    theory_results = []
    for solver_tag in base_solver_tags:
        if solver_tag == 'opensmt-2.5.2' and theory_tag in ['QF_NRA', 'QF_NIA']:
            continue
        print(f'solver {solver_tag}')
        def process_tag_result(tag):
            tag_result = ResultsProcesser.ProcessResults(f"{test_dir_path}/{tag}-all.csv", instance_list_path, time_limit)
            theory_results.append([tag, tag_result])
            res = count_results(tag, job_list, tag_result)
            sumups.append([tag, res['sat'], res['unsat'], res['solved'], res['failed'], res['PAR-2']])
            if all_results_dict.get(tag) == None:
                all_results_dict[tag] = {
                        'sat': 0, 'unsat': 0,
                        'solved': 0, 'failed': 0,
                        'PAR-2': 0.0, 
                    }
            
            tag_dict = all_results_dict[tag]
            tag_dict['sat'] += res['sat']
            tag_dict['unsat'] += res['unsat']
            tag_dict['solved'] += res['solved']
            tag_dict['failed'] += res['failed']
            tag_dict['PAR-2'] += res['PAR-2']
        
        if True:
            process_tag_result(f'{solver_tag}-p1')
            
        if core_number >= 8:
            process_tag_result(f'AriParti-{solver_tag}-p8')
            
        if core_number >= 16:
            process_tag_result(f'AriParti-{solver_tag}-p16')
    error_cnt = 0
    error_list_path = f'{statistics_dir_path}/{list_tag}-error_list.txt'
    with open(error_list_path, 'w') as outf:
        outf.write('Error instances are listed here.\n')
        
    for i in range(len(job_list)):
        job = job_list[i]
        is_error = False
        for j in range(len(theory_results)):
            resx = theory_results[j][1][i][0]
            if resx == 'failed':
                continue
            for k in range(j):
                resy = theory_results[k][1][i][0]
                if resy == 'failed':
                    continue
                if resx != resy:
                    is_error = True
                    break
            if is_error:
                break
        if is_error:
            error_cnt += 1
            print(f'error instance: {job_list[i]}')
            with open(error_list_path, mode="a") as outf:
                outf.write(f'{job} |')
                for solver_results in theory_results:
                    outf.write(f' ({solver_results[0]}, {solver_results[1][i][0]})')
                outf.write('\n')
    
    if error_cnt == 0:
        with open(f'{statistics_dir_path}/{list_tag}-error_list.txt', 'a') as outf:
            outf.write('No error is detected.\n')
    
    table = tabulate(sumups, headers="firstrow", tablefmt="fancy_grid")
    with open(f'{statistics_dir_path}/{list_tag}-results-sumup.txt', 'w') as outf:
        outf.write(f'{table}\n')

def AnalyzeResults(_test_tag: str, _lists_dir_path: str,
                   _core_number: int, _time_limit: float):
    global test_tag
    global statistics_dir_path
    global test_dir_path
    global instance_list_path
    global core_number
    global time_limit
    global all_results_dict
    
    test_tag = _test_tag
    statistics_dir_path      = f"AE-test-output/{_test_tag}/statistics"
    list_dir_path = _lists_dir_path
    core_number = _core_number
    time_limit = _time_limit
    
    all_results_dict = {}
    
    with open(f'{_lists_dir_path}/lists_list.txt', 'r') as inf:
        lines = inf.read().split('\n')
    
    for line in lines:
        if line == '':
            continue
        theory_tag, list_tag = line.split(' ')
        test_dir_path = f'{statistics_dir_path}/{list_tag}'
        instance_list_path = f'{list_dir_path}/{list_tag}.txt'
        process_theory(theory_tag, list_tag)
    
    all_theories_sumups = [['solver', 'sat', 'unsat', 'solved', 'failed', 'PAR-2']]
    for solver_tag in base_solver_tags:
        if True:
            tag = f'{solver_tag}-p1'
            res = all_results_dict[tag]
            all_theories_sumups.append([tag, res['sat'], res['unsat'], res['solved'], res['failed'], res['PAR-2']])
        
        if core_number >= 8:
            tag = f'AriParti-{solver_tag}-p8'
            res = all_results_dict[tag]
            all_theories_sumups.append([tag, res['sat'], res['unsat'], res['solved'], res['failed'], res['PAR-2']])
        
        if core_number >= 16:
            tag = f'AriParti-{solver_tag}-p16'
            res = all_results_dict[tag]
            all_theories_sumups.append([tag, res['sat'], res['unsat'], res['solved'], res['failed'], res['PAR-2']])
    
    table = tabulate(all_theories_sumups, headers="firstrow", tablefmt="fancy_grid")
    with open(f'{statistics_dir_path}/all-theories-results-sumup.txt', 'w') as outf:
        outf.write(f'{table}\n')

# collect_results(subset_tag, f'AE-test-output/{subset_tag}/lists/', core_number, time_limit)
if __name__ == "__main__":
    AnalyzeResults('subset_2_0.01_10', 'AE-test-output/subset_2_0.01_10/lists/',
                   128, 10.0)
    

'''

'''
