############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Z3 project configuration files
#
# Author: Leonardo de Moura (leonardo)
############################################
from mk_util import *

def init_version():
    set_version(4, 12, 2, 0) # express a default build version or pick up ci build version
    
# Z3 Project definition
def init_project_def():
    init_version()
    add_lib('util', [], includes2install = ['z3_version.h'])
    add_lib('polynomial', ['util'], 'math/polynomial')
    add_lib('interval', ['util'], 'math/interval')
    add_lib('automata', ['util'], 'math/automata')
    add_lib('params', ['util'])
    add_lib('subpaving', ['interval'], 'math/subpaving')
    add_lib('ast', ['util', 'polynomial'])
    add_lib('parser_util', ['ast'], 'parsers/util')
    add_lib('euf', ['ast'], 'ast/euf')
    add_lib('rewriter', ['ast', 'polynomial', 'interval', 'automata', 'params'], 'ast/rewriter')
    add_lib('normal_forms', ['rewriter'], 'ast/normal_forms')
    add_lib('substitution', ['rewriter'], 'ast/substitution')
    add_lib('proofs', ['rewriter'], 'ast/proofs')
    add_lib('macros', ['rewriter'], 'ast/macros')
    add_lib('model',  ['macros'])
    add_lib('converters', ['model'], 'ast/converters')
    add_lib('simplifiers', ['euf', 'normal_forms', 'converters', 'substitution'], 'ast/simplifiers')
    add_lib('tactic', ['simplifiers'])
    add_lib('solver', ['params', 'model', 'tactic', 'proofs'])
    add_lib('cmd_context', ['solver', 'rewriter', 'params'])
    add_lib('smt2parser', ['cmd_context', 'parser_util'], 'parsers/smt2')
    add_lib('pattern', ['normal_forms', 'smt2parser', 'rewriter'], 'ast/pattern')
    add_lib('core_tactics', ['tactic', 'macros', 'normal_forms', 'rewriter', 'pattern'], 'tactic/core')
    add_lib('arith_tactics', ['core_tactics'], 'tactic/arith')
    add_lib('subpaving_tactic', ['core_tactics', 'subpaving', "arith_tactics"], 'math/subpaving/tactic')
    add_lib('portfolio', ['subpaving_tactic'], 'tactic/portfolio')
    
    API_files = []
    add_exe('shell', ['portfolio'], exe_name='z3')
    add_js()
    return API_files


