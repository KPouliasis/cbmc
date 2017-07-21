/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H
#define CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H

#include <util/message.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

/// Selects the kind of allocation used by java_object_factory et al.
enum class allocation_typet {
  /// Allocate global objects
  GLOBAL,
  /// Allocate local stacked objects
  LOCAL,
  /// Allocate dynamic objects (using MALLOC)
  DYNAMIC
};

exprt object_factory(
  const typet &type,
  const irep_idt base_name,
  code_blockt &init_code,
  bool allow_null,
  symbol_tablet &symbol_table,
  size_t max_nondet_array_length,
  allocation_typet alloc_type,
  const source_locationt &);

enum class update_in_placet
{
  NO_UPDATE_IN_PLACE,
  MAY_UPDATE_IN_PLACE,
  MUST_UPDATE_IN_PLACE
};

void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const source_locationt &loc,
  bool skip_classid,
  allocation_typet alloc_type,
  bool assume_non_null,
  size_t max_nondet_array_length,
  update_in_placet update_in_place);

exprt allocate_dynamic_object(
  const exprt &target_expr,
  const typet &allocate_type,
  symbol_tablet &symbol_table,
  const source_locationt &loc,
  code_blockt &output_code,
  std::vector<const symbolt *> &symbols_created,
  bool cast_needed=false);

exprt allocate_dynamic_object_with_decl(
  const exprt &target_expr,
  const typet &allocate_type,
  symbol_tablet &symbol_table,
  const source_locationt &loc,
  code_blockt &output_code,
  bool cast_needed=false);

#endif // CPROVER_JAVA_BYTECODE_JAVA_OBJECT_FACTORY_H
