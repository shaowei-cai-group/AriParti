#!/usr/bin/python
import os

if os.path.exists('bin/partitioner'):
    os.system('rm bin/partitioner')
    print('remove exist partitioner binary file')

os.chdir('src/partitioner')
print(f'working directory {os.getcwd()}')
os.system('python scripts/mk_make.py')
os.chdir('build')
os.system('make -j')
os.chdir('../../../')
os.system('mv src/partitioner/build/z3 bin/partitioner')

print('build successfully')
