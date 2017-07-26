/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arrays.h"

#include <cassert>
#include <iostream>

#include <langapi/language_util.h>

#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/namespace.h>

#include <solvers/prop/prop.h>

arrayst::arrayst(
  const namespacet &_ns,
  propt &_prop):equalityt(_ns, _prop)
{
}

void arrayst::record_array_index(const index_exprt &index)
{
  // we are not allowed to put the index directly in the
  //   entry for the root of the equivalence class
  //   because this map is accessed during building the error trace
  collect_arrays(index.array());
  std::size_t number=arrays.number(index.array());
  index_map[number].insert(index.index());
}

literalt arrayst::record_array_equality(
  const equal_exprt &equality)
{
  const exprt &op0=equality.op0();
  const exprt &op1=equality.op1();

  // check types
  if(!base_type_eq(op0.type(), op1.type(), ns))
  {
    std::cout << equality.pretty() << '\n';
    throw "record_array_equality got equality without matching types";
  }

  INVARIANT(ns.follow(op0.type()).id()==ID_array,
            "equality has array type");

  std::size_t a1=arrays.number(op0);
  std::size_t a2=arrays.number(op1);

  array_equalities.push_back(array_equalityt());

  array_equalities.back().f1=op0;
  array_equalities.back().f2=op1;
  array_equalities.back().a1=a1;
  array_equalities.back().a2=a2;
  array_equalities.back().l=SUB::equality(op0, op1);

  collect_arrays(op0);
  collect_arrays(op1);

  return array_equalities.back().l;
}

void arrayst::collect_indices()
{
  for(std::size_t i=0; i<arrays.size(); i++)
  {
    collect_indices(arrays[i]);
  }
}

void arrayst::collect_indices(const exprt &expr)
{
  if(expr.id()!=ID_index)
  {
    forall_operands(op, expr) collect_indices(*op);
  }
  else
  {
    const index_exprt &e = to_index_expr(expr);
    collect_indices(e.index()); // necessary?

    const typet &array_op_type=ns.follow(e.array().type());

    if(array_op_type.id()==ID_array)
    {
      const array_typet &array_type=
        to_array_type(array_op_type);

      if(is_unbounded_array(array_type))
      {
        record_array_index(e);
      }
    }
  }
}

void arrayst::collect_arrays(const exprt &a)
{
  const array_typet &array_type=
    to_array_type(ns.follow(a.type()));

  if(a.id()==ID_with)
  {
    const with_exprt &with_expr=to_with_expr(a);

    // check types
    if(!base_type_eq(array_type, with_expr.old().type(), ns))
    {
      std::cout << a.pretty() << '\n';
      throw "collect_arrays got 'with' without matching types";
    }

    // record
    arrays.number(with_expr.old());
    collect_arrays(with_expr.old());
  }
  else if(a.id()==ID_update)
  {
    const update_exprt &update_expr=to_update_expr(a);

    // check types
    if(!base_type_eq(array_type, update_expr.old().type(), ns))
    {
      std::cout << a.pretty() << '\n';
      throw "collect_arrays got 'update' without matching types";
    }

    collect_arrays(update_expr.old());
  }
  else if(a.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(a);

    // check types
    if(!base_type_eq(array_type, if_expr.true_case().type(), ns))
    {
      std::cout << a.pretty() << '\n';
      throw "collect_arrays got if without matching types";
    }

    // check types
    if(!base_type_eq(array_type, if_expr.false_case().type(), ns))
    {
      std::cout << a.pretty() << '\n';
      throw "collect_arrays got if without matching types";
    }

    collect_arrays(if_expr.true_case());
    collect_arrays(if_expr.false_case());
  }
  else if(a.id()==ID_symbol)
  {
  }
  else if(a.id()==ID_nondet_symbol)
  {
  }
  else if(a.id()==ID_member)
  {
    if(to_member_expr(a).struct_op().id()!=ID_symbol)
      throw
        "unexpected array expression: member with `"+a.op0().id_string()+"'";
  }
  else if(a.id()==ID_constant ||
          a.id()==ID_array ||
          a.id()==ID_string_constant)
  {
  }
  else if(a.id()==ID_array_of)
  {
  }
  else if(a.id()==ID_byte_update_little_endian ||
          a.id()==ID_byte_update_big_endian)
  {
    assert(false);
  }
  else if(a.id()==ID_typecast)
  {
    // cast between array types?
    const exprt &op=to_typecast_expr(a).op();

    if(op.type().id()==ID_array)
    {
      collect_arrays(op);
    }
    else
      throw "unexpected array type cast from "+op.type().id_string();
  }
  else if(a.id()==ID_index)
  {
    // nested unbounded arrays
    collect_arrays(a.op0());
  }
  else
    throw "unexpected array expression (collect_arrays): `"+a.id_string()+"'";
}

bool arrayst::must_be_different(
  const exprt &x, const exprt &y)
{
  return false;
}

void arrayst::process_weg_path(const weg_patht &path)
{
  INVARIANT(!path.empty(), "path is not empty");
  wegt::node_indext a=path.front().n;
  wegt::node_indext b=path.back().n;

  // do constraints
  const index_sett &index_set_a=index_map[a];
  const index_sett &index_set_b=index_map[b];

  //std::cout << "b is: "
  //          << from_expr(ns, "", arrays[b])
  //          << '\n';

  for(const auto &index_a : index_set_a)
  {
    if(arrays[b].id()==ID_with)
    {
      // we got x=(y with [i:=v])
      const auto &expr_b=to_with_expr(arrays[b]);
      const exprt &index_b=expr_b.where();
      const exprt &value_b=expr_b.new_value();

      // 1. we got a[i]...b[j], given as edges on the stack
      // 2. add (i=j AND path_cond)=>a[i]=b[j]
      // 3. The path condition requires the update indices
      //    on the stack to be different from i.
      exprt::operandst cond;
      cond.reserve(path.size()+1);
      cond.push_back(equal_exprt(index_a, index_b));

      for(const auto &pn : path)
      {
        if(pn.n!=a) continue; // skip first one

        if(arrays[pn.n].id()==ID_with)
        {
          const auto &with_expr=to_with_expr(arrays[pn.n]);
          notequal_exprt inequality(with_expr.where(), index_a);
          cond.push_back(inequality);
        }
      }

      // a_i=b_i
      index_exprt a_i(arrays[a], index_a);
      // cond => a_i=b_i
      implies_exprt implication(
        conjunction(cond),
        equal_exprt(a_i, value_b));
      std::cout << "C2a: "
                << from_expr(ns, "", implication)
                << '\n';
      set_to_true(implication);
    }
    else if(arrays[b].id()==ID_array_of)
    {
      const auto &expr_b=to_array_of_expr(arrays[b]);
      const exprt &value_b=expr_b.what();

      // 1. we got a[i]...b[j], given as edges on the stack
      // 2. add (i=j AND path_cond)=>a[i]=b[j]
      // 3. The path condition requires the update indices
      //    on the stack to be different from i.
      exprt::operandst cond;
      cond.reserve(path.size());

      for(const auto &pn : path)
      {
        if(pn.n!=a) continue; // skip first one

        if(arrays[pn.n].id()==ID_with)
        {
          const auto &with_expr=to_with_expr(arrays[pn.n]);
          notequal_exprt inequality(with_expr.where(), index_a);
          cond.push_back(inequality);
        }
      }

      // a_i=value
      index_exprt a_i(arrays[a], index_a);
      // cond => a_i=b_i
      implies_exprt implication(
        conjunction(cond),
        equal_exprt(a_i, value_b));
      std::cout << "C2b: "
                << from_expr(ns, "", implication)
                << '\n';
      set_to_true(implication);
    }

    if(a!=b)
    {
      for(const auto &index_b : index_set_b)
      {
        if(must_be_different(index_a, index_b))
          continue;

        // 1. we got a[i]...b[j], given as edges on the stack
        // 2. add (i=j AND path_cond)=>a[i]=b[j]
        // 3. The path condition requires the update indices
        //    on the stack to be different from i.
        exprt::operandst cond;
        cond.reserve(path.size()+1);
        cond.push_back(equal_exprt(index_a, index_b));

        for(const auto &pn : path)
        {
          if(arrays[pn.n].id()==ID_with)
          {
            if(pn.n!=a) // skip if first node on path
            {
              const auto &with_expr=to_with_expr(arrays[pn.n]);
              notequal_exprt inequality(with_expr.where(), index_a);
              cond.push_back(inequality);
            }
          }
          #if 0
          else if(arrays[pn.n].id()==ID_if)
          {
            cond.push_back(false_exprt());
          }
          #endif
        }

        // a_i=b_i
        index_exprt a_i(arrays[a], index_a);
        index_exprt b_i(arrays[b], index_b);
        // cond => a_i=b_i
        implies_exprt implication(
          conjunction(cond),
          equal_exprt(a_i, b_i));
        std::cout << "C3: "
                  << from_expr(ns, "", implication)
                  << '\n';
        set_to_true(implication);
      }
    }
  }
}

void arrayst::add_array_constraints()
{
  for(const auto & a : arrays)
  {
    std::cout << "array: " << from_expr(ns, "", a)
              << '\n';
  }

  // build weak equivalence graph -- one node per array term
  weg.resize(arrays.size());

  // one undirected edge for each array equality
  for(const auto &eq : array_equalities)
    add_weg_edge(eq.a1, eq.a2, eq.l);

  for(std::size_t a_ind=0; a_ind<arrays.size(); a_ind++)
  {
    const exprt &a=arrays[a_ind];

    if(a.id()==ID_with)
    {
      // one undirected edge for each array update
      const auto &expr=to_with_expr(a);
      std::size_t expr_old_ind=arrays.number(expr.old());
      INVARIANT(expr_old_ind<weg.size(),
                "expr.old() already in 'arrays'");
      weg.add_undirected_edge(a_ind, expr_old_ind);
    }
    #if 1
    else if(a.id()==ID_if)
    {
      // we need two undirected edges for each 'if'
      const auto &expr=to_if_expr(a);
      std::size_t expr_true_ind=arrays.number(expr.true_case());
      std::size_t expr_false_ind=arrays.number(expr.false_case());
      INVARIANT(expr_true_ind<weg.size(),
                "expr.true_case() already in 'arrays'");
      INVARIANT(expr_false_ind<weg.size(),
                "expr.false_case() already in 'arrays'");
      literalt cond=convert(expr.cond());
      add_weg_edge(a_ind, expr_true_ind, cond);
      add_weg_edge(a_ind, expr_false_ind, !cond);
    }
    #endif
  }

  // auxiliary bit per node for DFS
  std::vector<bool> visited;
  visited.resize(weg.size());

  for(wegt::node_indext a=0; a<arrays.size(); a++)
  {
    std::cout << "a is: "
              << from_expr(ns, "", arrays[a])
              << '\n';

    // DFS from a_i to anything reachable in 'weg'
    std::fill(visited.begin(), visited.end(), false);

    weg_patht path;
    path.push_back(stack_entryt(a, weg[a].out.begin()));
    visited[a]=true;
    process_weg_path(path); // also process 'a' itself

    while(!path.empty())
    {
      // get next edge a->b
      stack_entryt &entry=path.back();
      if(entry.next==weg[entry.n].out.end())
      {
        path.pop_back();
        continue;
      }

      wegt::node_indext b=(entry.next++)->first;

      if(visited[b])
        continue; // already done it

      visited[b]=true;

      // add node 'b' to path
      path.push_back(stack_entryt(b, weg[b].out.begin()));

      // process
      process_weg_path(path);
    }
  }

  // add the Ackermann constraints
  add_array_Ackermann_constraints();
}

void arrayst::add_array_Ackermann_constraints()
{
  // this is quadratic!

#if 0
  std::cout << "arrays.size(): " << arrays.size() << '\n';
#endif

  // iterate over arrays
  for(std::size_t i=0; i<arrays.size(); i++)
  {
    const index_sett &index_set=index_map[i];

#if 0
    std::cout << "index_set.size(): " << index_set.size() << '\n';
#endif

    // iterate over indices, 2x!
    for(index_sett::const_iterator
        i1=index_set.begin();
        i1!=index_set.end();
        i1++)
      for(index_sett::const_iterator
          i2=index_set.begin();
          i2!=index_set.end();
          i2++)
        if(i1!=i2)
        {
          if(i1->is_constant() && i2->is_constant())
            continue;

          // index equality
          equal_exprt indices_equal(*i1, *i2);

          if(indices_equal.op0().type()!=
             indices_equal.op1().type())
          {
            indices_equal.op1().
              make_typecast(indices_equal.op0().type());
          }

          literalt indices_equal_lit=convert(indices_equal);

          if(indices_equal_lit!=const_literal(false))
          {
            const typet &subtype=ns.follow(arrays[i].type()).subtype();
            index_exprt index_expr1(arrays[i], *i1, subtype);

            index_exprt index_expr2=index_expr1;
            index_expr2.index()=*i2;

            equal_exprt values_equal(index_expr1, index_expr2);
            prop.lcnf(!indices_equal_lit, convert(values_equal));

            std::cout << "C4: "
                      << from_expr(ns, "", indices_equal)
                      << " => "
                      << from_expr(ns, "", values_equal)
                      << '\n';
          }
        }
  }
}

#if 0
void arrayst::add_array_constraints(
  const index_sett &index_set,
  const exprt &expr)
{
  if(expr.id()==ID_with)
    return add_array_constraints_with(index_set, to_with_expr(expr));
  else if(expr.id()==ID_update)
    return add_array_constraints_update(index_set, to_update_expr(expr));
  else if(expr.id()==ID_if)
    return add_array_constraints_if(index_set, to_if_expr(expr));
  else if(expr.id()==ID_array_of)
    return add_array_constraints_array_of(index_set, to_array_of_expr(expr));
  else if(expr.id()==ID_symbol ||
          expr.id()==ID_nondet_symbol ||
          expr.id()==ID_constant ||
          expr.id()=="zero_string" ||
          expr.id()==ID_array ||
          expr.id()==ID_string_constant)
  {
  }
  else if(expr.id()==ID_member &&
          to_member_expr(expr).struct_op().id()==ID_symbol)
  {
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    assert(0);
  }
  else if(expr.id()==ID_typecast)
  {
    // we got a=(type[])b
    assert(expr.operands().size()==1);

    // add a[i]=b[i]
    for(const auto &index : index_set)
    {
      const typet &subtype=ns.follow(expr.type()).subtype();
      index_exprt index_expr1(expr, index, subtype);
      index_exprt index_expr2(expr.op0(), index, subtype);

      assert(index_expr1.type()==index_expr2.type());

      // add constraint
      lazy_constraintt lazy(lazy_typet::ARRAY_TYPECAST,
        equal_exprt(index_expr1, index_expr2));
      add_array_constraint(lazy, false); // added immediately
    }
  }
  else if(expr.id()==ID_index)
  {
  }
  else
    throw
      "unexpected array expression (add_array_constraints): `"+
        expr.id_string()+"'";
}
#endif

#if 0
void arrayst::add_array_constraints_array_of(
  const index_sett &index_set,
  const array_of_exprt &expr)
{
  // we got x=array_of[v]
  // get other array index applications
  // and add constraint x[i]=v

  for(const auto &index : index_set)
  {
    const typet &subtype=ns.follow(expr.type()).subtype();
    index_exprt index_expr(expr, index, subtype);

    assert(base_type_eq(index_expr.type(), expr.op0().type(), ns));

    // add constraint
    lazy_constraintt lazy(
      lazy_typet::ARRAY_OF, equal_exprt(index_expr, expr.op0()));
    add_array_constraint(lazy, false); // added immediately
  }
}
#endif

#if 0
void arrayst::add_array_constraints_if(
  const index_sett &index_set,
  const if_exprt &expr)
{
  // we got x=(c?a:b)
  literalt cond_lit=convert(expr.cond());

  // get other array index applications
  // and add c => x[i]=a[i]
  //        !c => x[i]=b[i]

  // first do true case

  for(const auto &index : index_set)
  {
    const typet subtype=ns.follow(expr.type()).subtype();
    index_exprt index_expr1(expr, index, subtype);
    index_exprt index_expr2(expr.true_case(), index, subtype);

    // add implication
    lazy_constraintt lazy(lazy_typet::ARRAY_IF,
                            or_exprt(literal_exprt(!cond_lit),
                              equal_exprt(index_expr1, index_expr2)));
    add_array_constraint(lazy, false); // added immediately

#if 0 // old code for adding, not significantly faster
    prop.lcnf(!cond_lit, convert(equal_exprt(index_expr1, index_expr2)));
#endif
  }

  // now the false case
  for(const auto &index : index_set)
  {
    const typet subtype=ns.follow(expr.type()).subtype();
    index_exprt index_expr1(expr, index, subtype);
    index_exprt index_expr2(expr.false_case(), index, subtype);

    // add implication
    lazy_constraintt lazy(
      lazy_typet::ARRAY_IF,
      or_exprt(literal_exprt(cond_lit),
      equal_exprt(index_expr1, index_expr2)));
    add_array_constraint(lazy, false); // added immediately

#if 0 // old code for adding, not significantly faster
    prop.lcnf(cond_lit, convert(equal_exprt(index_expr1, index_expr2)));
#endif
  }
}
#endif
