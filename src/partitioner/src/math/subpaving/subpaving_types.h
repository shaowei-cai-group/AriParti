/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_types.h

Abstract:

    Subpaving auxiliary types.

Author:

    Leonardo de Moura (leonardo) 2012-08-07.

Revision History:

--*/
#pragma once

namespace subpaving {

class atom;

struct lit {
    unsigned    m_x:28;
    unsigned    m_lower:1;
    unsigned    m_open:1;
    unsigned    m_bool:1;    
    unsigned    m_int:1;    
    mpq *       m_val;
};

struct task_info {
    unsigned m_node_id;
    unsigned m_depth;
    unsigned m_undef_lit_num;
    unsigned m_undef_clause_num;
    vector<vector<lit>>  m_clauses;
    vector<lit>  m_var_bounds;
    
    void reset() {
        m_node_id = UINT32_MAX;
        m_clauses.reset();
        m_var_bounds.reset();
        m_undef_lit_num = 0;
        m_undef_clause_num = 0;
    }
};

typedef unsigned var;

const var null_var = UINT_MAX;

class exception {
};

class power : public std::pair<var, unsigned> {
public:
    power() = default;
    power(var v, unsigned d):std::pair<var, unsigned>(v, d) {}
    var x() const { return first; }
    var get_var() const { return first; }
    unsigned degree() const { return second; }
    unsigned & degree() { return second; }
    void set_var(var x) { first = x; }
    struct lt_proc { bool operator()(power const & p1, power const & p2) { return p1.get_var() < p2.get_var(); } };
};

struct display_var_proc {
    virtual ~display_var_proc() = default;
    virtual void operator()(std::ostream & out, var x) const { out << "x" << x; }
};

}
