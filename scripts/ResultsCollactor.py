#!/usr/bin/python

# collect results with list

import os
import ListJobCollector

class Information:
    def __init__(self, n) -> None:
        self.name = n
        self.all_counter = 0
        self.mp_counter = {"solved" : 0, "unsolved" : 0}
    def collect(self, result) -> None:
        self.all_counter = self.all_counter + 1 
        if result in self.mp_counter:
            self.mp_counter[result] = self.mp_counter[result] + 1
        else:
            self.mp_counter[result] = 1
        if result == "sat" or result == "unsat":
            self.mp_counter["solved"] = self.mp_counter["solved"] + 1
        else:
            self.mp_counter["unsolved"] = self.mp_counter["unsolved"] + 1

def solve_job(job):
    result = ""
    cost_time = time_limit
    with open(input_dir_path + job, mode="r", encoding="utf-8") as inf:
        lines = inf.read().split('\n')
    result = lines[0]
    if result not in ['sat', 'unsat']:
        result = 'failed'
        cost_time = time_limit
    else:
        cost_time = float(lines[1])

    with open(f"{output_dir_path}/{solve_tag}-all.csv", mode="a", encoding="utf-8") as all_job_file:
        all_job_file.write(f"{job},{result},{cost_time}\n")
    
    all_job_info.collect(result)



def CollectResults(_test_type: str, _list_tag: str, _solve_tag: str,
                   _lists_dir_path: str, _time_limit: float):
    
    global solve_tag
    global input_dir_path
    global output_dir_path
    global time_limit
    
    solve_tag           = _solve_tag
    instance_list_path  = f'{_lists_dir_path}/{_list_tag}.txt'
    input_dir_path      = f"AE-test-output/{_test_type}/raw-results/{_list_tag}/{_solve_tag}"
    output_dir_path     = f"AE-test-output/{_test_type}/statistics/{_list_tag}/"

    time_limit = _time_limit

    os.system("mkdir -p " + output_dir_path)
    jobs_list = ListJobCollector.CollectListJobs(instance_list_path)
    # print(jobs_list)
    with open(f"{output_dir_path}/{solve_tag}-all.csv", mode="w", encoding="utf-8") as all_job_file:
        all_job_file.write("file path,result,cost time\n")
    global all_job_info
    all_job_info = Information("all instances")
    for job in jobs_list:
        solve_job(job)
    
    with open(f"{output_dir_path}/{solve_tag}-sumup.txt", mode="w", encoding="utf-8") as fsumup:
        fsumup.write(f"{all_job_info.mp_counter}\n")
    
if __name__ == "__main__":
    CollectResults('subset_2_0.01_10', 'QF_LIA-subset_2_0.01_list-132', 'AriParti-cvc5-1.0.8-p8', 'AE-test-output/subset_2_0.01_10/lists', 10.0)

'''

'''
