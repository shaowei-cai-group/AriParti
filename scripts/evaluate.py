import os
import argparse
import logging
import GenerateTestListsRandomly
import time
import datetime
import RIWLBaseSolver
import RIWLAriParti
import ResultsCollactor
import ResultsAnalyzer

def make_dir(dir):
    os.system('mkdir -p ' + dir)

benchmark_tags = {
    'QF_LIA': 'QF_LIA-13226',
    'QF_LRA': 'QF_LRA-1753',
    'QF_NIA': 'QF_NIA-25358',
    'QF_NRA': 'QF_NRA-12134',
}

base_solver_tags = [
    'cvc5-1.0.8',
    'opensmt-2.5.2',
    'z3-4.12.1',
]

def test_solvers(test_tag: str, lists_dir_path: str, core_number: int, time_limit: float):
    with open(f'{lists_dir_path}/lists_list.txt', 'r') as inf:
        lines = inf.read().split('\n')
    for line in lines:
        if line == '':
            continue
        theory_tag, list_tag = line.split(' ')
        print(theory_tag, list_tag)
        logging.info(f'testing: theory {theory_tag}, list {list_tag}')
        benchmark_tag = benchmark_tags[theory_tag]
        
        for solver_tag in base_solver_tags:
            if solver_tag == 'opensmt-2.5.2' and theory_tag in ['QF_NRA', 'QF_NIA']:
                continue
            RIWLBaseSolver.RIWL_BaseSolver(core_number, benchmark_tag,
                                            list_tag, solver_tag, test_tag, 
                                            lists_dir_path, time_limit)
            logging.info(f'test finised: solver {solver_tag}, p1')
            if core_number >= 8:
                RIWLAriParti.RIWL_AriParti(8, core_number // 8, benchmark_tag,
                                            list_tag, solver_tag, test_tag, 
                                            lists_dir_path, time_limit)
                logging.info(f'test finised: AriParti with solver {solver_tag}, p8')
            
            if core_number >= 16:
                RIWLAriParti.RIWL_AriParti(16, core_number // 16, benchmark_tag,
                                            list_tag, solver_tag, test_tag, 
                                            lists_dir_path, time_limit)
                logging.info(f'test finised: AriParti with solver {solver_tag}, p16')

def collect_results(test_tag: str, lists_dir_path: str, core_number: int, time_limit: float):
    with open(f'{lists_dir_path}/lists_list.txt', 'r') as inf:
        lines = inf.read().split('\n')
    for line in lines:
        if line == '':
            continue
        theory_tag, list_tag = line.split(' ')
        print(theory_tag, list_tag)
        logging.info(f'collecting: theory {theory_tag}, list {list_tag}')
        
        for solver_tag in base_solver_tags:
            if solver_tag == 'opensmt-2.5.2' and theory_tag in ['QF_NRA', 'QF_NIA']:
                continue
            ResultsCollactor.CollectResults(test_tag, list_tag, f'{solver_tag}-p1', 
                                            lists_dir_path, time_limit)
            logging.info(f'collect finised: solver {solver_tag}, p1')
            if core_number >= 8:
                ResultsCollactor.CollectResults(test_tag, list_tag, f'AriParti-{solver_tag}-p8', 
                                                lists_dir_path, time_limit)
                logging.info(f'collect finised: AriParti with solver {solver_tag}, p8')
            
            if core_number >= 16:
                ResultsCollactor.CollectResults(test_tag, list_tag, f'AriParti-{solver_tag}-p16', 
                                                lists_dir_path, time_limit)
                logging.info(f'collect finised: AriParti with solver {solver_tag}, p16')

if __name__ == '__main__':
    start_time = time.time()
    
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument('--test-type', type=str, required=True,
                            help="test type: smoke, subset, all")
    arg_parser.add_argument('--core-number', type=int, required=True,
                            help="number of cores in this machine")
    arg_parser.add_argument('--time-limit', type=float, required=False, default=120.0,
                            help="time limit for each instance solving (second)")
    arg_parser.add_argument('--seed', type=int, required=False, default=0,
                            help="random seed")
    arg_parser.add_argument('--ratio', type=str, required=False, default= '0.05',
                            help="instance selection ratio")
    args = arg_parser.parse_args()
    
    test_type: str = args.test_type
    time_limit: float = args.time_limit
    core_number: int = args.core_number
    
    if test_type == 'smoke':
        test_tag = 'smoke'
        lists_dir_path = 'benchmark-lists/smoke-test'
    elif test_type == 'subset':
        seed: int = args.seed
        ratio: str = args.ratio
        test_tag = f'subset_{seed}_{ratio}_{time_limit:.0f}'
        lists_dir_path = f'AE-test-output/{test_tag}/lists'
        print('Subset instances random selecting')
        GenerateTestListsRandomly.RandomSelectSubset(seed, ratio, time_limit)
    elif test_type == 'all':
        test_tag = f'all_{time_limit:.0f}'
        lists_dir_path = 'benchmark-lists/all'
    
    make_dir(f'AE-test-output/{test_tag}')
    logging.basicConfig(format='%(relativeCreated)d - %(levelname)s - %(message)s', 
                        filename=f'AE-test-output/{test_tag}/{test_tag}.log', level=logging.INFO)
    logging.info(f'{test_tag} test start')
    
    test_solvers(test_tag, lists_dir_path, core_number, time_limit)
    collect_results(test_tag, lists_dir_path, core_number, time_limit)
    
    print(f'analyzing start')
    logging.info(f'analyzing start')
    ResultsAnalyzer.AnalyzeResults(test_tag, lists_dir_path, core_number, time_limit)
    
    end_time = time.time()
    cost_time = end_time - start_time
    
    print('Evaluation finished')
    print(f'Cost time: {datetime.timedelta(seconds=cost_time)}')
    print('Results are located in dir AE-test-output')
    
    logging.info('Evaluation finished')
    logging.info(f'Cost time: {datetime.timedelta(seconds=cost_time)}')
    logging.info('Results are located in dir AE-test-output')

