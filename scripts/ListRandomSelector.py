import ListJobCollector
import random

def RandomSelectList(seed: int, ratio: float, input_list_path: str):
    random.seed(seed)
    jobs_list = ListJobCollector.CollectListJobs(input_list_path)
    ret = []
    for job in jobs_list:
        if random.random() <= ratio:
            ret.append(job)
    if len(ret) == 0:
        ret.append(jobs_list[0])
    return ret
    