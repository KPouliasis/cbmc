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
  lazy_arrays = false;        // will be set to true when --refine is used
  incremental_cache = false;  // for incremental solving
}

void arrayst::record_array_index(const index_exprt &index)
{
  // we are not allowed to put the index directly in the
  //   entry for the root of the equivalence class
  //   because this map is accessed during building the error trace
  std::size_t number=arrays.number(index.array());
  index_map[number].insert(index.index());
  update_indices.insert(number);
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

  assert(ns.follow(op0.type()).id()==ID_array);

  array_equalities.push_back(array_equalityt());

  array_equalities.back().f1=op0;
  array_equalities.back().f2=op1;
  array_equalities.back().l=SUB::equality(op0, op1);

  arrays.make_union(op0, op1);
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

    arrays.make_union(a, with_expr.old());
    collect_arrays(with_expr.old());

    // make sure this shows as an application
    index_exprt index_expr(with_expr.old(), with_expr.where());
    record_array_index(index_expr);
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

    arrays.make_union(a, update_expr.old());
    collect_arrays(update_expr.old());

#if 0
    // make sure this shows as an application
    index_exprt index_expr(update_expr.old(), update_expr.index());
    record_array_index(index_expr);
#endif
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

    arrays.make_union(a, if_expr.true_case());
    arrays.make_union(a, if_expr.false_case());
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
    assert(0);
  }
  else if(a.id()==ID_typecast)
  {
    // cast between array types?
    assert(a.operands().size()==1);

    if(a.op0().type().id()==ID_array)
    {
      arrays.make_union(a, a.op0());
      collect_arrays(a.op0());
    }
    else
      throw "unexpected array type cast from "+a.op0().type().id_string();
  }
  else if(a.id()==ID_index)
  {
    // nested unbounded arrays
    arrays.make_union(a, a.op0());
    collect_arrays(a.op0());
  }
  else
    throw "unexpected array expression (collect_arrays): `"+a.id_string()+"'";
}

/// adds array constraints (refine=true...lazily for the refinement loop)
void arrayst::add_array_constraint(const lazy_constraintt &lazy, bool refine)
{
  if(lazy_arrays && refine)
  {
    // lazily add the constraint
    if(incremental_cache)
    {
      if(expr_map.find(lazy.lazy) == expr_map.end())
      {
        lazy_array_constraints.push_back(lazy);
        expr_map[lazy.lazy] = true;
      }
    }
    else
    {
      lazy_array_constraints.push_back(lazy);
    }
  }
  else
  {
    // add the constraint eagerly
    prop.l_set_to_true(convert(lazy.lazy));
  }
}

void arrayst::add_array_constraints()
{
  collect_indices();
  // at this point all indices should in the index set

  // reduce initial index map
  update_index_map(true);

  // add constraints for if, with, array_of
  for(std::size_t i=0; i<arrays.size(); i++)
  {
    // take a copy as arrays may get modified by add_array_constraints
    // in case of nested unbounded arrays
    exprt a=arrays[i];

    add_array_constraints(index_map[arrays.find_number(i)], a);

    // we have to update before it gets used in the next add_* call
    update_index_map(false);
  }

  // add constraints for equalities
  for(const auto &equality : array_equalities)
  {
    add_array_constraints_equality(
      index_map[arrays.find_number(equality.f1)],
      equality);

    // update_index_map should not be necessary here
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
    const index_sett &index_set=index_map[arrays.find_number(i)];

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

            // add constraint
            lazy_constraintt lazy(lazy_typet::ARRAY_ACKERMANN,
              or_exprt(literal_exprt(!indices_equal_lit), values_equal));
            add_array_constraint(lazy, true); // added lazily

#if 0 // old code for adding, not significantly faster
            prop.lcnf(!indices_equal_lit, convert(values_equal));
#endif
          }
        }
  }
}

/// merge the indices into the root
void arrayst::update_index_map(std::size_t i)
{
  if(arrays.is_root_number(i))
    return;

  std::size_t root_number=arrays.find_number(i);
  assert(root_number!=i);

  index_sett &root_index_set=index_map[root_number];
  index_sett &index_set=index_map[i];

  root_index_set.insert(index_set.begin(), index_set.end());
}

void arrayst::update_index_map(bool update_all)
{
  // iterate over non-roots
  // possible reasons why update is needed:
  //  -- there are new equivalence classes in arrays
  //  -- there are new indices for arrays that are not the root
  //     of an equivalence class
  //     (and we cannot do that in record_array_index())
  //  -- equivalence classes have been merged
  if(update_all)
  {
    for(std::size_t i=0; i<arrays.size(); i++)
      update_index_map(i);
  }
  else
  {
    for(const auto &index : update_indices)
      update_index_map(index);

    update_indices.clear();
  }

#ifdef DEBUG
  // print index sets
  for(const auto &index_entry : index_map)
    for(const auto &index : index_entry.second)
      std::cout << "Index set (" << index_entry.first << " = "
                << arrays.find_number(index_entry.first) << " = "
                << from_expr(ns, "",
                             arrays[arrays.find_number(index_entry.first)])
                << "): "
                << from_expr(ns, "", index) << '\n';
  std::cout << "-----\n";
#endif
}

void arrayst::add_array_constraints_equality(
  const index_sett &index_set,
  const array_equalityt &array_equality)
{
  // add constraints x=y => x[i]=y[i]

  for(const auto &index : index_set)
  {
    const typet &subtype1=ns.follow(array_equality.f1.type()).subtype();
    index_exprt index_expr1(array_equality.f1, index, subtype1);

    const typet &subtype2=ns.follow(array_equality.f2.type()).subtype();
    index_exprt index_expr2(array_equality.f2, index, subtype2);

    assert(index_expr1.type()==index_expr2.type());

    array_equalityt equal;
    equal.f1 = index_expr1;
    equal.f2 = index_expr2;
    equal.l = array_equality.l;
    equal_exprt equality_expr(index_expr1, index_expr2);

    // add constraint
    // equality constraints are not added lazily
    // convert must be done to guarantee correct update of the index_set
    prop.lcnf(!array_equality.l, convert(equality_expr));
  }
}

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

void arrayst::add_array_constraints_with(
  const index_sett &index_set,
  const with_exprt &expr)
{
  // we got x=(y with [i:=v])
  // add constraint x[i]=v

  const exprt &index=expr.where();
  const exprt &value=expr.new_value();

  {
    index_exprt index_expr(expr, index, ns.follow(expr.type()).subtype());

    if(index_expr.type()!=value.type())
    {
      std::cout << expr.pretty() << '\n';
      assert(false);
    }

    lazy_constraintt lazy(
       lazy_typet::ARRAY_WITH, equal_exprt(index_expr, value));
     add_array_constraint(lazy, false); // added immediately
  }

  // use other array index applications for "else" case
  // add constraint x[I]=y[I] for I!=i

  for(auto other_index : index_set)
  {
    if(other_index!=index)
    {
      // we first build the guard

      if(other_index.type()!=index.type())
        other_index.make_typecast(index.type());

      literalt guard_lit=convert(equal_exprt(index, other_index));

      if(guard_lit!=const_literal(true))
      {
        const typet &subtype=ns.follow(expr.type()).subtype();
        index_exprt index_expr1(expr, other_index, subtype);
        index_exprt index_expr2(expr.op0(), other_index, subtype);

        equal_exprt equality_expr(index_expr1, index_expr2);

        // add constraint
        lazy_constraintt lazy(lazy_typet::ARRAY_WITH, or_exprt(equality_expr,
                                literal_exprt(guard_lit)));
        add_array_constraint(lazy, false); // added immediately

#if 0 // old code for adding, not significantly faster
        {
          literalt equality_lit=convert(equality_expr);

          bvt bv;
          bv.reserve(2);
          bv.push_back(equality_lit);
          bv.push_back(guard_lit);
          prop.lcnf(bv);
        }
#endif
      }
    }
  }
}

void arrayst::add_array_constraints_update(
  const index_sett &index_set,
  const update_exprt &expr)
{
  // we got x=UPDATE(y, [i], v)
  // add constaint x[i]=v

#if 0
  const exprt &index=expr.where();
  const exprt &value=expr.new_value();

  {
    index_exprt index_expr(expr, index, ns.follow(expr.type()).subtype());

    if(index_expr.type()!=value.type())
    {
      std::cout << expr.pretty() << '\n';
      assert(false);
    }

    set_to_true(equal_exprt(index_expr, value));
  }

  // use other array index applications for "else" case
  // add constraint x[I]=y[I] for I!=i

  for(auto other_index : index_set)
  {
    if(other_index!=index)
    {
      // we first build the guard

      if(other_index.type()!=index.type())
        other_index.make_typecast(index.type());

      literalt guard_lit=convert(equal_exprt(index, other_index));

      if(guard_lit!=const_literal(true))
      {
        const typet &subtype=ns.follow(expr.type()).subtype();
        index_exprt index_expr1(expr, other_index, subtype);
        index_exprt index_expr2(expr.op0(), other_index, subtype);

        equal_exprt equality_expr(index_expr1, index_expr2);

        literalt equality_lit=convert(equality_expr);

        // add constraint
        bvt bv;
        bv.reserve(2);
        bv.push_back(equality_lit);
        bv.push_back(guard_lit);
        prop.lcnf(bv);
      }
    }
  }
#endif
}

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
