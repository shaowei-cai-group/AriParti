import os
import random
import argparse
import ListJobCollector

all_list_tags = [
    'QF_LRA-all_list-1753',
    'QF_LIA-all_list-13226',
    'QF_NRA-all_list-12134',
    'QF_NIA-all_list-25358',
]

def RandomSelectList(seed: int, ratio: float, input_list_path: str):
    random.seed(seed)
    jobs_list = ListJobCollector.CollectListJobs(input_list_path)
    ret = []
    for job in jobs_list:
        if random.random() <= ratio:
            ret.append(job)
    return ret

def RandomSelectSubset(_seed: int, _ratio: str, _time_limit: float):
    # print('Subset instances random selecting')
    seed:int = _seed
    ratio:float = float(_ratio)
    
    subset_tag = f'subset_{seed}_{ratio}_{_time_limit:.0f}'
    os.system(f'mkdir -p AE-test-output/{subset_tag}/lists')
    if os.path.exists(f'AE-test-output/{subset_tag}/lists/lists_list.txt'):
        os.system(f'rm AE-test-output/{subset_tag}/lists/lists_list.txt')
        
    for list_tag in all_list_tags:
        theory_tag = list_tag[: list_tag.find('-')]
        subset_list = RandomSelectList(seed, ratio, f'benchmark-lists/all/{list_tag}.txt')
        print(f'{len(subset_list)} instances in {theory_tag}')
        theory_list_name = f'{theory_tag}-subset_{seed}_{ratio}_list-{len(subset_list)}'
        with open(f'AE-test-output/{subset_tag}/lists/lists_list.txt', mode='a') as of:
            of.write(f'{theory_tag} {theory_list_name}\n')
        
        with open(f'AE-test-output/{subset_tag}/lists/{theory_list_name}.txt', mode='w') as of:
            for job in subset_list:
                of.write(f'{job}\n')

if __name__ == '__main__':
    # arg_parser = argparse.ArgumentParser()
    # arg_parser.add_argument('--seed', type=int, required=True,
    #                         help="random seed")
    # arg_parser.add_argument('--ratio', type=str, required=True,
    #                         help="instance selection ratio")
    # args = arg_parser.parse_args()
    # _seed: int = args.seed
    # _ratio: str = args.ratio
    # RandomSelectSubset(_seed, _ratio)
    
    RandomSelectSubset(0, 0.005)