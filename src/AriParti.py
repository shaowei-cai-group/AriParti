#!/usr/bin/python
import os
import time
import argparse
import subprocess

class Task():
    
    def __init__(self, p, id, parent, make_time):
        self.p = p
        self.id = id
        self.parent = parent
        self.make_time = make_time
        self.start_time = -1
        # waiting running sat unsat unknown
        # waiting -> running BY (run task)
        #         -> unsat   BY (ancester, children, partitioner)
        #         -> unknown BY (children)
        # running -> sat BY (solver)
        #         -> unsat BY (solver, ancester, children, partitioner)
        #         -> unknown BY (solver, children)
        self.state = 'waiting'
        self.reason = -3
        self.subtasks = []
        
    def __str__(self) -> str:
        pid = -1
        if (self.parent != None):
            pid = self.parent.id
        ret = f'id: {self.id}'
        ret += f', make-time: {self.make_time:.2f}'
        ret += f', parent: {pid}'
        ret += f', state: {self.state}'
        if self.start_time != -1:
            ret += f', start_time: {self.start_time:.2f}'
        if self.reason != -3:
            ret += f', reason: {self.reason}'
        if len(self.subtasks) > 0:
            stid = []
            stid.append(self.subtasks[0].id)
            if len(self.subtasks) > 1:
                stid.append(self.subtasks[1].id)
            ret += f', subtasks: {stid}'
        return ret

class ArithPartition():
    
    def init_params(self):
        arg_parser = argparse.ArgumentParser()
        arg_parser.add_argument('--file', type=str, required=True,
                                help="input instance file path")
        arg_parser.add_argument('--output-dir', type=str, required=True,
                                help="output dir path")
        arg_parser.add_argument('--partitioner', type=str, required=True,
                                help="partitioner path")
        arg_parser.add_argument('--solver', type=str, required=True,
                                help="solver path")
        arg_parser.add_argument('--max-running-tasks', type=int, default=32, 
                                help="maximum number of tasks running simultaneously")
        arg_parser.add_argument('--time-limit', type=int, default=0, 
                                help="time limit, 0 means no limit")
        
        args = arg_parser.parse_args()
        
        self.input_file_path : str = args.file
        self.output_dir_path : str = args.output_dir
        self.partitioner_path : str = args.partitioner
        self.solver_path : str = args.solver
        self.max_running_tasks : int = args.max_running_tasks
        self.time_limit : int = args.time_limit
        
        self.instance_name : str = self.input_file_path[ \
            self.input_file_path.rfind('/') + 1 : self.input_file_path.find('.smt2')]
    
    def init_communication(self):
        self.need_communicate = True
        
        write_pipe_path = f'{self.output_dir_path}/master-to-partitioner'
        read_pipe_path = f'{self.output_dir_path}/partitioner-to-master'
        log_file_path = f'{self.output_dir_path}/log'
        
        temp_file = open(read_pipe_path, "w")
        temp_file.close()
        
        self.write_pipe = open(write_pipe_path, 'w')
        self.read_pipe = open(read_pipe_path, 'r')
        self.log_file = open(log_file_path, 'w')
        
        self.start_time = time.time()
        self.write_line_to_partitioner(f"start-time {self.start_time}")
        
        
    
    def write_line_to_log(self, data : str):
        curr_time : int = int(time.time() - self.start_time)
        line : str = f'{curr_time} {data}\n'
        self.log_file.write(line)
        self.log_file.flush()
        
    
    def write_line_to_partitioner(self, data : str):
        curr_time : int = int(time.time() - self.start_time)
        line : str = f'{curr_time} {data}\n'
        self.write_pipe.write(line)
        self.write_pipe.flush()
        self.write_line_to_log(data)
    
    def read_line_from_partitioner(self):
        res = self.read_pipe.readline().strip('\n')
        return res
        
    
    def init(self):
        self.init_params()
        self.task_head = 0
        self.id2task = {}
        self.tasks = []
        self.running_tasks = []
        self.result = "undefined"
        self.reason = -3
        self.done = False
        self.base_run_cnt = 0
        
        self.run_ori_flag = True

        os.system("mkdir -p " + f"{self.output_dir_path}")
        os.system("mkdir -p " + f"{self.output_dir_path}/tasks")
        
        self.init_communication()
        
    def clean_up(self):
        # if os.path.exists(f'{self.output_dir_path}'):
        #     os.system(f'rm -r {self.output_dir_path}')
        if os.path.exists(f'{self.output_dir_path}/tasks'):
            os.system(f'rm -r {self.output_dir_path}/tasks')
    
    def make_task(self, id, pid, is_unsat):
        parent : Task = None
        if (pid != -1):
            parent = self.id2task[pid]
        t = Task(None, id, parent, self.get_current_time())
        
        if is_unsat:
            t.state = 'unsat'
            t.reason = -1
            if parent != None:
                self.push_up(parent, t.id)
        
        if parent != None:
            if t.state != 'unsat' and parent.state == 'unsat':
                self.propagate_unsat(t, parent.reason)
            parent.subtasks.append(t)
        
        self.write_line_to_log(f'make-task {t}')
        
        self.id2task[id] = t
        self.tasks.append(t)

    def run_task(self, t : Task):
        task_path = f'{self.output_dir_path}/tasks/task-{t.id}.smt2'
        cmd =  [self.solver_path,
                task_path
            ]
        p = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
        t.p = p
        t.state = "running"
        t.start_time = self.get_current_time()
        self.running_tasks.append(t)
        self.write_line_to_log(f'run-task {t.id}')
        self.write_line_to_log(f'runnings {len(self.running_tasks)}')
        self.write_line_to_log(f'waitings {len(self.tasks) - self.task_head}')
    
    def parse_line(self, line : str):
        words = line.split(' ')
        op = words[1]
        if op == 'debug-info':
            remains = " ".join(words[2 : ])
            self.write_line_to_log(f'partitioner-debug-info {remains}')
        elif op in ['new-task', 'unsat-task']:
            id = int(words[2])
            pid = int(words[3])
            if op == 'new-task':
                is_unsat = False
            else:
                is_unsat = True
            self.make_task(id, pid, is_unsat)
            
        else:
            assert(False)

    def read_parse_line(self):
        line = self.read_line_from_partitioner()
        if line == "":
            return False
        self.parse_line(line)
        return True
        
    def communicate_with_partitioner(self):
        while self.read_parse_line():
            pass
        if self.partitioner.state != 'running':
            self.write_line_to_log(f'partitioner-done {self.partitioner.state}')
            self.need_communicate = False

    def check_process(self, id, p : subprocess.Popen):
        rc = p.poll()
        if rc == None:
            return 'running'
        out_data, err_data = p.communicate()
        ret : str = out_data.strip('\n').strip(' ')
        if rc != 0:
            ret = 'non-zero-return'
        self.write_line_to_log(f'task-done {id} {ret}')
        return ret
        
    
    def propagate_unsat(self, t : Task, reason):
        assert(t.state != 'unsat')
        if t.p != None and t.state != 'terminated':
            self.write_line_to_log(f'terminated-by-propagate {t.id} {reason}')
            t.p.terminate()
        t.state = 'unsat'
        t.reason = reason
        self.write_line_to_partitioner(f'unsat-node {t.id}')
    
    def push_up(self, t : Task, reason):
        # only 'unsat' 'unknown' need push up
        if t.state == 'unsat':
            return
        if len(t.subtasks) == 2 and \
           t.subtasks[0].state == 'unsat' and \
           t.subtasks[1].state == 'unsat':
            self.write_line_to_log(f'unsat-by-children {t.id} {t.subtasks[0].id} {t.subtasks[1].id}')
            self.propagate_unsat(t, reason)
            if t.parent != None:
                self.push_up(t.parent, reason)

    def push_down(self, t : Task, reason):
        # only 'unsat' need push up
        if t.state == 'unsat':
            return
        self.propagate_unsat(t, reason)
        self.write_line_to_log(f'unsat-by-ancestor {t.id} {reason}')
        for st in t.subtasks:
            self.push_down(st, reason)
            
    def need_terminate(self, t : Task):
        if t.id <= 0:
            return False
        
        num_st = len(t.subtasks)
        st_end = 0
        if num_st > 0 and t.subtasks[0].state != 'waiting':
            st_end += 1
        if num_st > 1 and t.subtasks[1].state != 'waiting':
            st_end += 1
        
        if st_end == 0:
            return False
        if st_end == 1 and self.get_current_time() - t.start_time < 200.0:
            return False
        if st_end == 2 and self.get_current_time() - t.start_time < 100.0:
            return False
        return True
    
    def terminate_task(self, t : Task):
        t.state = 'terminated'
        if t.p != None:
            t.p.terminate()
        self.write_line_to_partitioner(f'terminate-node {t.id}')
    
    def check_runnings_state(self):
        if self.run_ori_flag and self.ori_task.state == 'running':
            sta = self.check_process(self.ori_task.id, self.ori_task.p)
            if sta != 'running':
                if sta in ['sat', 'unsat']:
                    self.result = sta
                    self.done = True
                    self.write_line_to_log(f'solved-by-original {sta}')
                    return
                self.ori_task.state = sta
                self.base_run_cnt -= 1
        
        if self.partitioner.state == 'running':
            sta = self.check_process(self.partitioner.id, self.partitioner.p)
            if sta != 'running':
                if sta in ['sat', 'unsat']:
                    self.result = sta
                    self.done = True
                    self.write_line_to_log(f'solved-by-partitioner {sta}')
                    return
                self.partitioner.state = sta

        still_runnings = []
        for t in self.running_tasks:
            t : Task
            assert(t.state != 'waiting')
            if t.state in ['unsat', 'unknown', 'terminated']:
                continue
            sta = self.check_process(t.id, t.p)
            if sta == 'running':
                if self.need_terminate(t):
                    self.terminate_task(t)
                else:
                    still_runnings.append(t)
                continue
            if sta == 'sat':
                self.result = 'sat'
                self.reason = t.id
                self.done = True
                self.write_line_to_log(f'sat-task {t.id}')
                return
            t.reason = t.id
            if sta == 'unsat':
                t.state = 'unsat'
                self.write_line_to_partitioner(f'unsat-node {t.id}')
                if t.parent != None:
                    self.push_up(t.parent, t.id)
                for st in t.subtasks:
                    # st : Task
                    self.push_down(st, t.id)
            else:
                t.state = sta
                self.write_line_to_partitioner(f'unknown-node {t.id} {sta}')
                
        self.running_tasks = still_runnings
        if len(self.tasks) > 0:
            root_task : Task = self.tasks[0]
            if root_task.state == 'unsat':
                self.result = 'unsat'
                self.reason = root_task.reason
                self.done = True
                self.write_line_to_log(f'unsat-root-task {root_task.reason}')
                return
        
        if self.partitioner.state != 'running' and \
            len(self.running_tasks) == 0 and \
            self.result not in ['sat', 'unsat']:
            
            self.result = 'unknown'
            self.reason = -3
            self.done = True
            if self.run_ori_flag:
                if self.ori_task.state == 'running':
                    self.write_line_to_log(f'unknown partitioner bug')
                else:
                    self.write_line_to_log(f'unknown instance bug')
            return
    
    # run waitings by:
    # currently: generation order
    # can be easily change to: priority
    def run_waiting_tasks(self):
        sz = len(self.tasks)
        while self.task_head < sz:
            if len(self.running_tasks) + self.base_run_cnt >= self.max_running_tasks:
                break
            t : Task = self.tasks[self.task_head]
            if t.state == 'waiting':
                self.run_task(t)
            self.task_head += 1
    
    def get_current_time(self):
        return time.time() - self.start_time
    
    def run_partitioner(self):
        cmd =  [self.partitioner_path,
                self.input_file_path, 
                f"-outputdir:{self.output_dir_path}",
                f"-partmrt:{self.max_running_tasks}"
            ]
        p = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
        self.partitioner = Task(p, -1, None, self.get_current_time())
        self.partitioner.state = "running"
        self.partitioner.start_time = self.get_current_time()
    
    def run_ori_task(self):
        # run original task
        cmd =  [self.solver_path,
                self.input_file_path
            ]
        # print(" ".join(cmd))
        p = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
        self.ori_task = Task(p, -2, None, self.get_current_time())
        self.ori_task.state = "running"
        self.ori_task.start_time = self.get_current_time()
        self.base_run_cnt += 1
    
    def solve(self):
        if self.run_ori_flag:
            self.run_ori_task()
        self.run_partitioner()
        while True:
            if self.need_communicate:
                self.communicate_with_partitioner()
            self.check_runnings_state()
            if self.done:
                return
            self.run_waiting_tasks()
            
            if self.get_current_time() >= self.time_limit:
                raise TimeoutError()
            
            if len(self.running_tasks) + self.base_run_cnt >= self.max_running_tasks \
                or (not self.need_communicate):
                time.sleep(0.1)
        
    
    def sum_up(self, result, exec_time):
        with open(f"{self.output_dir_path}/result.txt", "w") as f:
            f.write(f"{result}\n{exec_time}\n")
        
    def terminate_all(self):
        if self.run_ori_flag:
            self.ori_task.p.terminate()
        self.partitioner.p.terminate()
        for t in self.tasks:
            p : subprocess.Popen = t.p
            if p == None:
                continue
            p.terminate()
    
    def __call__(self):
        self.init()
        try:
            self.solve()
        except TimeoutError:
            self.result = "timeout"
            self.write_line_to_log(f'timeout')
        except AssertionError:
            self.result = 'AssertionError'
        
        print(self.result)
        
        end_time = time.time()
        execution_time = end_time - self.start_time
        
        print(execution_time)
        
        self.sum_up(self.result, execution_time)
        
        self.terminate_all()
        self.clean_up()
        

if __name__ == "__main__":
    ap = ArithPartition()
    ap()
    
'''

'''
