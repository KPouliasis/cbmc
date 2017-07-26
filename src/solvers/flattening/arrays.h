/*******************************************************************\

Module: Theory of Arrays with Extensionality

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Theory of Arrays with Extensionality

#ifndef CPROVER_SOLVERS_FLATTENING_ARRAYS_H
#define CPROVER_SOLVERS_FLATTENING_ARRAYS_H

#include <set>

#include <util/numbering.h>
#include <util/graph.h>

#include "equality.h"

class array_of_exprt;
class equal_exprt;
class if_exprt;
class index_exprt;
class with_exprt;
class update_exprt;

class arrayst:public equalityt
{
public:
  arrayst(const namespacet &_ns, propt &_prop);

  void post_process() override
  {
    post_process_arrays();
    SUB::post_process();
  }

  // NOLINTNEXTLINE(readability/identifiers)
  typedef equalityt SUB;

  literalt record_array_equality(const equal_exprt &expr);
  void record_array_index(const index_exprt &expr);

protected:
  virtual void post_process_arrays()
  {
    add_array_constraints();
  }

  // adds all the constraints eagerly
  void add_array_constraints();
  void add_array_Ackermann_constraints();
  void collect_arrays(const exprt &);
  void collect_indices();
  void collect_indices(const exprt &);

  class weg_edget
  {
  public:
    literalt condition;
  };

  // weak equality graph
  class weg_nodet:public graph_nodet<weg_edget>
  {
    exprt array;
  };

  typedef grapht<weg_nodet> wegt;
  wegt weg;
  
  void add_weg_edge(std::size_t a1, std::size_t a2, literalt l)
  {
    weg.edge(a1, a2).condition=l;
    weg.edge(a2, a1).condition=l;
  }

  struct array_equalityt
  {
    literalt l;
    exprt f1, f2;
    std::size_t a1, a2;
  };

  // the list of all equalities between arrays
  // references to objects in this container need to be stable as
  // elements are added while references are held
  typedef std::list<array_equalityt> array_equalitiest;
  array_equalitiest array_equalities;

  // this is used to give a unique number to all arrays
  typedef numbering<exprt> array_numberingt;
  array_numberingt arrays;

  // this tracks the array indicies for each array
  typedef std::set<exprt> index_sett;
  typedef std::map<std::size_t, index_sett> index_mapt;
  index_mapt index_map;

  virtual bool is_unbounded_array(const typet &type) const=0;
    // (maybe this function should be partially moved here from boolbv)

  bool must_be_different(const exprt &, const exprt &);

  // path search
  struct stack_entryt
  {
    wegt::node_indext n;
    wegt::edgest::const_iterator next;
    stack_entryt(
      wegt::node_indext _n,
      wegt::edgest::const_iterator _next):n(_n), next(_next)
    {
    }
  };

  typedef std::vector<stack_entryt> weg_patht;
  void process_weg_path(const weg_patht &);

  //bool incremental_cache;

  #if 0
  void add_array_constraints_equality(
    const index_sett &index_set, const array_equalityt &array_equality);
  void add_array_constraints(
    const index_sett &index_set, const exprt &expr);
  void add_array_constraints_if(
    const index_sett &index_set, const if_exprt &exprt);
  void add_array_constraints_with(
    const index_sett &index_set, const with_exprt &expr);
  void add_array_constraints_update(
    const index_sett &index_set, const update_exprt &expr);
  void add_array_constraints_array_of(
    const index_sett &index_set, const array_of_exprt &exprt);
  #endif
};

#endif // CPROVER_SOLVERS_FLATTENING_ARRAYS_H
