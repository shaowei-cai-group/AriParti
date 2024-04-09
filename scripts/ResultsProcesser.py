import ListJobCollector
    
def ProcessResults(input_file: str, instance_list_path: str, time_limit: float):
    job_list = ListJobCollector.CollectListJobs(instance_list_path)
    
    input_datas = {}
    with open(input_file, 'r') as inf:
        rows = inf.read().split('\n')
        # print(rows[0])
        if rows[0][0] != '/':
            rows[1: ]
        for row in rows:
            items = row.split(',')
            state = 'failed'
            cost_time = time_limit
            if len(items) > 1 and items[1] in ['sat', 'unsat']:
                state = items[1]
                cost_time = items[2]
            input_datas[items[0]] = [state, cost_time]

    ret = []
    for job in job_list:
        state = 'failed'
        cost_time = time_limit
        if job in input_datas:
            state = input_datas[job][0]
            cost_time = input_datas[job][1]
        else:
            print(f'missing result: {input_file} {job}')
        ret.append([state, cost_time])
    return ret