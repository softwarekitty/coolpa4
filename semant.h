#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>  
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"
#include <map>

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
private:
  std::map<Symbol, Class_> *class_table;
  int semant_errors;
  void install_basic_classes();
  ostream& error_stream;


public:
  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);
  void install_class(Symbol id, Class_ cls);
  void initialize_class_contents();
  void initialize_inheritance_tree();
  void validate_classes();
  void validate_features();
  bool isMismatchedOverride(Feature cmethod, Feature pmethod);
  bool identicalFormals(Formals f1, Formals f2);
};

// reducing clutter in semant.cc
Features join3_Features(Feature f1, Feature f2, Feature f3){
    return append_Features(append_Features(single_Features(f1),single_Features(f2)),single_Features(f3));
}
Features join4_Features(Feature f1, Feature f2, Feature f3, Feature f4){
    return append_Features(join3_Features(f1,f2,f3),single_Features(f4));
}
Features join5_Features(Feature f1, Feature f2, Feature f3, Feature f4, Feature f5){
    return append_Features(join4_Features(f1,f2,f3,f4),single_Features(f5));
}

#endif

