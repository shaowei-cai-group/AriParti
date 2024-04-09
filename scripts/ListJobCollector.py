
def CollectListJobs(instance_list_path: str):
    with open(instance_list_path, mode='r', encoding='utf-8') as inf:
        ret = inf.read().split('\n')
    ret = [j for j in ret if j != '']
    if len(ret) > 0 and ret[0][0] != '/':
        ret = ret[1: ]
    # print('job size:', len(ret))
    return ret
    