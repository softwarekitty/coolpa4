

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;

static std::ostringstream oss;
static void wipe(){
    oss.str("");
    oss.clear();
}


//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}



ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr){

    //first install the built-ins (this is an abbreviated version 
    //of install_base_classes from the SKEL file)
    class_table = new std::map<Symbol, Class_>;
    Symbol basic_class_filename = stringtable.add_string("<basic class>");
    install_class(
        Object, 
        class_(Object, No_class,
            join3_Features(
                method(cool_abort, nil_Formals(), Object, no_expr()),
                method(type_name, nil_Formals(), Str, no_expr()),
                method(copy, nil_Formals(), SELF_TYPE, no_expr())),basic_class_filename)
	);
	install_class(
        Bool, 
        class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),basic_class_filename)
    );
    install_class(
        Int, 
        class_(Int, Object,single_Features(attr(val, prim_slot, no_expr())),basic_class_filename)
    );
    install_class(
        IO, 
        class_(IO, Object,
            join4_Features(
                method(out_string, single_Formals(formal(arg, Str)),SELF_TYPE, no_expr()),
                method(out_int, single_Formals(formal(arg, Int)),SELF_TYPE, no_expr()),
                method(in_string, nil_Formals(), Str, no_expr()),
                method(in_int, nil_Formals(), Int, no_expr())),basic_class_filename)
    );
    install_class(
        Str, 
        class_(Str, Object,
            join5_Features(
                attr(val, Int, no_expr()),
                attr(str_field, prim_slot, no_expr()),
                method(length, nil_Formals(), Int, no_expr()),
                method(concat,single_Formals(formal(arg, Str)),Str, no_expr()),
                method(substr,append_Formals(single_Formals(formal(arg, Int)), single_Formals(formal(arg2, Int))),Str,no_expr())
            ),basic_class_filename)
    );
    
    //now install all the classes given as arguments
    for(int i = classes->first(); classes->more(i); i = classes->next(i)) {
        install_class(classes->nth(i)->get_name(), classes->nth(i));
    }
}

void ClassTable::install_class(Symbol id, Class_ cls){
    if (class_table->find(id) != class_table->end()) {
        semant_error(cls);
        wipe(); oss << "Class " << id << " already exists" << endl;
        throw oss.str();
    }else if (id == SELF_TYPE) {
        semant_error(cls);
        wipe(); oss << "Class cannot have name SELF_TYPE" << endl;
        throw oss.str();
    }
    class_table->insert(std::pair<Symbol, Class_>(id, cls));
}

void ClassTable::initialize_class_contents(){
    for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
        it->second->initialize_contents();
    }
}

void ClassTable::initialize_inheritance_tree(){
    for(std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++){
        if(!(it->second->get_parent() == No_class)){
            std::map<Symbol, Class_>::iterator it2;
            Symbol parent = it->second->get_parent();
            if((it2 = class_table->find(parent)) == class_table->end()){
                wipe(); oss << "The class " << it->second->get_name() << " has parent: "<< parent << " which was not found."<< endl;
                throw oss.str();
            }else{
                it2->second->add_child(it->second);
            }
        }
    }
}

void ClassTable::validate_classes(){

    // require the presence of of Main and Object
    if(class_table->find(Main) == class_table->end()){
        wipe(); oss << "Main class missing from class table"<<endl;
        throw oss.str();
    }else if(class_table->find(Object) == class_table->end()){
        wipe(); oss << "Object class missing from class table"<<endl;
        throw oss.str();
    }else{

        // require that all classes descending from object are visited only once.
        class_table->find(Object)->second->validate_inheritanceR();
        
        //require that every class descends from Object
        for(std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++){
            if(!(it->second->isVisited())){
                wipe(); oss << "Class " << it->second->get_name() << " was never visited, and is therefore detached from Object"<<endl;
                throw oss.str();
            }
        }
    }
}

void ClassTable::validate_features(){
    for(std::map<Symbol, Class_>::iterator cit = class_table->begin(); cit != class_table->end(); cit++){
    
        //for each non-root class...
        Class_ child = cit->second;
        Symbol parent_sym = child->get_parent();
        Class_ parent = class_table->find(parent_sym)->second;
        if(!(parent_sym == No_class)){
        
            //check for mismatched override methods...
            std::map<Symbol, Feature> *cmtable = child->mtable(); 
            for (std::map<Symbol, Feature>::iterator mit = cmtable->begin(); mit != cmtable->end(); mit++){
                std::map<Symbol, Feature> *pmtable = parent->mtable();
                Feature cmethod = mit->second;
                if(pmtable->find(cmethod->get_name()) != pmtable->end()){
                    Feature pmethod = pmtable->find(cmethod->get_name())->second;
                    if(isMismatchedOverride(cmethod,pmethod)){
                        wipe(); oss << "method with name "<< cmethod->get_name() << " in class " << child << " is mismatched with a method with the same name from parent class: " << parent<<endl;
                        throw oss.str();
                    }
                }
            }
            
            //and check for redefined attributes
            SymbolTable<Symbol, Symbol> *potable = parent->otable();
            Features cfeatures = child->getFeatures();
            for (int i = cfeatures->first(); cfeatures->more(i); i = cfeatures->next(i)) {
                Feature f = cfeatures->nth(i);
                if(!f->isMethod() && potable->probe(f->get_name()) != NULL){
                    wipe(); oss << "attribute with name "<< f->get_name() << " in class " << child << " is also defined in parent class: " << parent<<endl;
                    throw oss.str();
                }
            }
        }
    }
}

bool ClassTable::isMismatchedOverride(Feature cmethod, Feature pmethod){
        if(!cmethod->isMethod() || !pmethod->isMethod()){
            return false;
        }if(cmethod->get_name() != pmethod->get_name()){
            return false;
        }else if(cmethod->get_type() != pmethod->get_type()){
            return true;
        }else if(!identicalFormals(cmethod->get_formals(), pmethod->get_formals())){
            return true;
        }else{
            return false;
        }
   }

bool ClassTable::identicalFormals(Formals f1, Formals f2){
    if(f1->len() != f2->len()){
        return false;
    }else{
        for(int i = f1->first(); f1->more(i); i=f1->next(i)){
            if((f1->nth(i)->get_type() != f2->nth(i)->get_type()) ||
            (f1->nth(i)->get_name() != f2->nth(i)->get_name())){
                return false;                
            }
        } 
    }
    return true;
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 

//////////////////////////////////////initializers////////////////////////////////////
void class__class::initialize_contents(){
    if(semant_debug){cout<<"initializing class contents" << endl;}
    for(int i = features->first(); features->more(i); i = features->next(i)) {
        features->nth(i)->initialize(this);
    }
}

void method_class::initialize(Class_ c){
    if(c->mtable()->find(name) != c->mtable()->end()){
        wipe(); oss << name << " is not a unique method name within " << c->get_name();
        throw oss.str();     
    }else if(name == self){
        wipe(); oss << "illegal method name: " << name << " within: " << c->get_name();
        throw oss.str();
    }
    if(semant_debug){cout<<"initializing method: " << name << endl;}
    c->mtable()->insert(std::pair<Symbol, Feature>(name, this));    
}

void attr_class::initialize(Class_ c){
    if(c->otable()->probe(name)){
        wipe(); oss << name << " is not a unique attribute name within " << c->get_name();
        throw oss.str();
    } else if (name == self){
        wipe(); oss << "illegal attribute name: " << name << " within: " << c->get_name();
        throw oss.str();
    }
    if(semant_debug){cout<<"initializing attr contents for: " << name << " with type: "<< type_decl << endl;}
    c->otable()->addid(name, new Symbol(type_decl));
}

void class__class::validate_inheritanceR(){
    if(isVisited()){
        wipe(); oss << "Class " << name << " has been visited more than once in a tree traversal, which indicates a cycle is present";
        throw oss.str();
    }else{
        visit();
        for(std::list<Class_>::iterator it = child_list->begin(); it != child_list->end(); it++){
            (*it)-> validate_inheritanceR();
        }
    }
}




///////////////////////////////////////semants////////////////////////////////////////
void formal_class::semant(){}

void static_dispatch_class::semant(){}
void branch_class::semant(){}
void assign_class::semant(){}
void cond_class::semant(){}
void leq_class::semant(){}
void lt_class::semant(){}
void eq_class::semant(){}
void loop_class::semant(){}
void typcase_class::semant(){}
void block_class::semant(){}
void let_class::semant(){}
void plus_class::semant(){}
void sub_class::semant(){}
void mul_class::semant(){}
void neg_class::semant(){}
void comp_class::semant(){}
void bool_const_class::semant(){}
void string_const_class::semant(){}
void object_class::semant(){}
void no_expr_class::semant(){}
void isvoid_class::semant(){}
void new__class::semant(){}
void int_const_class::semant(){}
void divide_class::semant(){}
void dispatch_class::semant(){}

void class__class::semant()
{
    if(semant_debug){cout<<"class semant"<<endl;}
  for(int i = features->first(); features->more(i); i = features->next(i)) {
    features->nth(i)->semant();
  }
}

void method_class::semant(){if(semant_debug){cout<<"method semant"<<endl;}}
void attr_class::semant(){if(semant_debug){cout<<"attr semant"<<endl;}}

/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();
    ClassTable *classtable;
    try{
        //install all classes
        classtable = new ClassTable(classes);
        
        // record attr and methods
        classtable->initialize_class_contents();
        
        // record what children classes have
        classtable->initialize_inheritance_tree();
        
        // make sure that the classes are well formed
        classtable->validate_classes();
        
        // check methods and attributes for problems
        classtable->validate_features();
        
        /* recursively call semant on nodes in the tree, recovering to catch more errors */
        for(int i = classes->first(); classes->more(i); i = classes->next(i)) {
            Class_ current_class = classes->nth(i);
            try{
                current_class->semant();
            }catch(std::string error_msg){
                classtable->semant_error(current_class);
                cerr << error_msg << endl;
            }
        }
    }catch(std::string error_msg){
        classtable->semant_error();
        cerr << error_msg << endl;
    }

    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }
}


