

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;


//global vars used for generating error reports
static std::ostringstream oss;
static void wipe(){
    oss.str("");
    oss.clear();
}
ClassTable *classtable;
Class_ semant_class;


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
static void initialize_constants(void){
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
        wipe(); oss << "Class " << id << " is duplicated" << endl;
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

//true if s1 <= s2
bool ClassTable::inherits(Symbol s1, Symbol s2){
    


    if(s1 == No_type || s2 == No_type || (s1==SELF_TYPE && s2==SELF_TYPE)
    || s1 == s2 || (s1==SELF_TYPE && semant_class->get_name() == s2)){
        return true;
    }else if (s2 == SELF_TYPE){
        if(semant_debug){cerr<<s1<<" does not inherit "<<s2<<" because s2 is SELF_TYPE"<<endl;}
        return false;
    }else{
        if(s1==SELF_TYPE){
            s1 = semant_class->get_name();
        }
        if(!classExists(s1)){
            if(semant_debug){cerr<<s1<<" does not inherit "<<s2<<" because s1 does not exist"<<endl;}
            //TODO -error
            return false;
        }else if(!classExists(s2)){
            if(semant_debug){cerr<<s1<<" does not inherit "<<s2<<" because s2 does not exist"<<endl;}
            //TODO -error
            return false;
        }else{
            Symbol p1 = getClass(s1)->get_parent();
            if(p1==No_class){
                if(semant_debug){cerr<<s1<<" does not inherit "<<s2<<" because s1's parent is No_class"<<endl;}
                return false;
            }else{
                return inherits(p1,s2);
            }
        }
    }
}

bool ClassTable::classExists(Symbol s1){
    return class_table->find(s1) != class_table->end();
}

//assumes that s1 exists
Class_ ClassTable::getClass(Symbol s1){
    if(s1==SELF_TYPE){
        s1 = semant_class->get_name();
    }
    return class_table->find(s1)->second;
}

void ClassTable::addToCurrentScope(Symbol name, Symbol type){
    SymbolTable<Symbol, Symbol> *otable = semant_class->otable();
    if(name==self){
        classtable->semant_error(semant_class);
        //TODO - error
    }else if(otable->probe(name)){
        classtable->semant_error(semant_class);
        //TODO - error
    }else{
        otable->addid(name, new Symbol(type));
    }
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

ostream& ClassTable::semant_error(Class_ c){      
    if(semant_debug){cout<<"semant_error called with class: "<<c->get_name()<<endl;}                                                       
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t){
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error(){                                                 
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

Symbol class__class::get_attr(Symbol s1){
    Symbol *stype = object_table->lookup(s1);
    if(stype != NULL){
        return *stype;
    }else if(get_parent() == No_class){
        return NULL;
    }else{
        return classtable->getClass(get_parent())->get_attr(s1);
    }
}

Feature class__class::get_method(Symbol method){
    std::map<Symbol, Feature>::iterator it = method_table->find(method);
    if(it!=method_table->end()){
         return it->second;
    }else if(get_parent() != No_class){
        return classtable->getClass(get_parent())->get_method(method);
    }else{
        return NULL;
    }
}


///////////////////////////////////////semants////////////////////////////////////////
void isvoid_class::semant(){e1->semant();type=Bool;}
void no_expr_class::semant(){type=No_type;}
void bool_const_class::semant(){type = Bool;}
void string_const_class::semant(){type = Str;}
void int_const_class::semant(){type = Int;}
void object_class::semant(){
    if(name==self){type=SELF_TYPE;}
    else{
        Symbol t = semant_class->get_attr(name);
        if(t==NULL){
            classtable->semant_error(semant_class);
            cerr << "object cannot be found in scope: "<<name<<endl;
        }else{
            type = t;
        }
    }
}
void new__class::semant(){
    if(semant_debug){cerr<<"begin semant in new__class"<<endl;}
    if(!classtable->classExists(type_name)){
        classtable->semant_error(semant_class);
        cerr << "class: "<<type_name<<" cannot be found"<<endl;
        type=No_type;
    }else{
        type=type_name;
    }
}

void dispatch_class::semant(){
    if(semant_debug){cerr<<"begin semant in dispatch_class"<<endl;}
    expr->semant();
    Class_ caller = classtable->getClass(expr->get_type());
    Feature method = caller->get_method(name);
    if(method==NULL){
        classtable->semant_error(semant_class);
        cerr << "method: "<<name<<" cannot be found in class: "<<caller<<endl;
    }else if(method->get_formals()->len() != actual->len()){
        classtable->semant_error(semant_class);
        cerr << "method: "<<name<<" has "<<method->get_formals()->len()<<" arguments, but is called with "<<actual->len()<<endl;
    }else{
        for(int i= actual->first(); actual->more(i); i=actual->next(i)){
            actual->nth(i)->semant();
            Symbol ftype = method->get_formals()->nth(i)->get_type();
            if(!classtable->inherits(actual->nth(i)->get_type(), ftype)){
                classtable->semant_error(semant_class);
                cerr << "method arg "<<i+1<<" should be of type: "<<ftype<<" but is of type: "<<actual->nth(i)->get_type()<<endl;
            }       
        }
        Symbol t = method->get_type();
        if(t==SELF_TYPE){
            type=expr->get_type();
        }else{
            type=t;
        }
    }
    if(semant_debug){cerr<<"finish semant in dispatch_class"<<endl;}
}
void static_dispatch_class::semant(){
    if(semant_debug){cerr<<"begin semant in static_dispatch_class"<<endl;}
    expr->semant();
    if(!classtable->inherits(expr->get_type(), type_name)){
        classtable->semant_error(semant_class);
        cerr << "type mismatch in static dispatch: "<<endl;
    }else{
        Class_ caller = classtable->getClass(expr->get_type());
        Feature method = caller->get_method(name);
        if(method==NULL){
            classtable->semant_error(semant_class);
            cerr << "method: "<<name<<" cannot be found in class: "<<caller<<endl;
        }else if(method->get_formals()->len() != actual->len()){
            classtable->semant_error(semant_class);
            cerr << "method: "<<name<<" has "<<method->get_formals()->len()<<" arguments, but is called with "<<actual->len()<<endl;
        }else{
            for(int i= actual->first(); actual->more(i); i=actual->next(i)){
                actual->nth(i)->semant();
                Symbol ftype = method->get_formals()->nth(i)->get_type();
                if(!classtable->inherits(actual->nth(i)->get_type(), ftype)){
                    classtable->semant_error(semant_class);
                    cerr << "method arg "<<i+1<<" should be of type: "<<ftype<<" but is of type: "<<actual->nth(i)->get_type()<<endl;
                }       
            }
            Symbol t = method->get_type();
            if(t==SELF_TYPE){
                type=expr->get_type();
            }else{
                type=t;
            }
        }
    }
    if(semant_debug){cerr<<"finish semant in static_dispatch_class"<<endl;}
}

void typcase_class::semant(){
    if(semant_debug){cerr<<"begin semant in typcase_class"<<endl;}
    type=Object;
    //TODO
}

void let_class::semant(){
    if(semant_debug){cerr<<"begin semant in let_class"<<endl;}
    SymbolTable<Symbol, Symbol> *otable = semant_class->otable();
    init->semant();
    otable->enterscope();
    if(!classtable->classExists(type_decl)){
        classtable->semant_error(semant_class);
        cerr<<"type does not exist"<<endl;
    }else{
        classtable->addToCurrentScope(identifier, type_decl);
    }
    body->semant();
    if(!classtable->inherits(init->get_type(), type_decl)){
        classtable->semant_error(semant_class);
        cerr<<"init type does not inherit declared type"<<endl;
    }else{
        type=body->get_type();
    }
    otable->exitscope();
}

void plus_class::semant(){
    if(semant_debug){cerr<<"begin semant in plus_class"<<endl;}
    e1->semant();
    e2->semant();
    if(e1->get_type() != Int || e2->get_type() != Int){
        classtable->semant_error(semant_class);
        cerr << "both arguments for plus must be Ints"<<endl;
    }else{
        type=Int;
    }
}

void eq_class::semant(){
    if(semant_debug){cerr<<"begin semant in eq_class"<<endl;}
    e1->semant();
    e2->semant();
    Symbol e1_type = e1->get_type();
    Symbol e2_type = e2->get_type();
    if((e1_type==Int||e1_type== Bool||e1_type==Str||e2_type==Int||e2_type==Bool||e2_type==Str)
 	    &&e1_type!=e2_type){
        classtable->semant_error(semant_class);
        cerr << "cannot compare with equals the types: "<<e1->get_type()<<" and "<<e2->get_type()<<endl;	
 	}else{
 	    type=Bool;
 	}
}

void mul_class::semant(){
    if(semant_debug){cerr<<"begin semant in  mul_class"<<endl;}
    e1->semant();
    e2->semant();
    if(e1->get_type() != Int || e2->get_type() != Int){
        classtable->semant_error(semant_class);
        cerr << "both arguments for multiply must be Ints"<<endl;
    }else{
        type=Int;
    }
}

void divide_class::semant(){
    if(semant_debug){cerr<<"begin semant in div_class"<<endl;}
    e1->semant();
    e2->semant();
    if(e1->get_type() != Int || e2->get_type() != Int){
        classtable->semant_error(semant_class);
        cerr << "both arguments for divide must be Ints"<<endl;
    }else{
        type=Int;
    }
}

void sub_class::semant(){
    if(semant_debug){cerr<<"begin semant in sub_class"<<endl;}
    e1->semant();
    e2->semant();
    if(e1->get_type() != Int || e2->get_type() != Int){
        classtable->semant_error(semant_class);
        cerr << "both arguments for subtract must be Ints"<<endl;
    }else{
        type=Int;
    }
}

void neg_class::semant(){
    if(semant_debug){cerr<<"begin semant in neg_class"<<endl;}
    e1->semant();
    if(e1->get_type() != Int){
        classtable->semant_error(semant_class);
        cerr << "the argument for negation must be an Int"<<endl;
    }else{
        type=Int;
    }
}
void comp_class::semant(){
    if(semant_debug){cerr<<"begin semant in comp_class"<<endl;}
    e1->semant();
    if(e1->get_type() != Bool){
        classtable->semant_error(semant_class);
        cerr << "the argument for complementation must be a Bool"<<endl;
    }else{
        type=Bool;
    }
}

void lt_class::semant(){
    if(semant_debug){cerr<<"begin semant in lt_class"<<endl;}
    e1->semant();
    e2->semant();
    if(e1->get_type() != Int || e2->get_type() != Int){
        classtable->semant_error(semant_class);
        cerr << "both arguments for less than must be Ints"<<endl;
    }else{
        type=Bool;
    }
}
void leq_class::semant(){
    if(semant_debug){cerr<<"begin semant in leq_class"<<endl;}
    e1->semant();
    e2->semant();
    if(e1->get_type() != Int || e2->get_type() != Int){
        classtable->semant_error(semant_class);
        cerr << "both arguments for less than or equals must be Ints"<<endl;
    }else{
        type=Bool;
    }
}


void block_class::semant(){
    if(semant_debug){cerr<<"begin semant in block_class"<<endl;}
    for(int i=body->first();body->more(i); i=body->next(i)){
        body->nth(i)->semant();
        type = body->nth(i)->get_type();
    }
}

void branch_class::semant(){
    if(semant_debug){cerr<<"begin semant in branch_class"<<endl;}
    SymbolTable<Symbol, Symbol> *otable = semant_class->otable();
    otable->enterscope();
    if(classtable->classExists(type_decl)){
        classtable->addToCurrentScope(name,type_decl);
    }else{
        classtable->semant_error(semant_class);
        cerr<<"type does not exist: "<<type_decl<<endl;
    }
    expr->semant();
    otable->exitscope();
}

void loop_class::semant(){
    if(semant_debug){cerr<<"begin semant in loop_class"<<endl;}
    pred->semant();
    body->semant();
    if (pred->get_type() != Bool) {
        classtable->semant_error(semant_class);
        cerr<<"pred must be Bool"<<endl; 
    }
    type=Object;
    //TODO...
}


void cond_class::semant(){
    if(semant_debug){cerr<<"begin semant in cond_class"<<endl;}
    pred->semant();
    then_exp->semant();
    else_exp->semant();
    if (pred->get_type() != Bool) {
        classtable->semant_error(semant_class);
        cerr<<"condition must have type Bool"<<endl;
    }else{
        type=Object;
        //TODO...lub
    }
}

void assign_class::semant(){
    if(semant_debug){cerr<<"begin semant in assign_class"<<endl;}
    expr->semant();
    
    Symbol assign_type = semant_class->get_attr(name);
    if(assign_type==NULL){
        classtable->semant_error(semant_class);
        cerr<<"assign type does not exist"<<endl;
    }else if(!classtable->inherits(expr->get_type(), assign_type)){
        classtable->semant_error(semant_class);
        cerr<<"assignment inheritance problem"<<endl;     
    }else{
        type=expr->get_type();
    }
    if(semant_debug){cerr<<"complete semant in assign_class"<<endl;}
}



void formal_class::semant(){
    if(semant_debug){cerr<<"begin semant in formal_class"<<endl;}
    if(type_decl == SELF_TYPE){
        cerr<<"formal has type==SELF_TYPE"<<endl;
    }
    if(!classtable->classExists(type_decl)){
        classtable->semant_error(semant_class);
        cerr<<"class in formal does not exist"<<endl; 
    }else{
        classtable->addToCurrentScope(name,type_decl);
    }
}

void method_class::semant(){
    if(semant_debug){cerr<<"begin semant in method_class"<<endl;}
    SymbolTable<Symbol, Symbol> *otable = semant_class->otable();
    //enter the scope of the method
    otable->enterscope();
    
    //call semant on child nodes
    for(int i = formals->first(); formals->more(i); i = formals->next(i)) {
        formals->nth(i)->semant();
    }
    expr->semant();
    
    //check validity of expr
    Symbol t = expr->get_type();
    if(semant_debug){cerr<<"checking minherits for: "<<t<<" and "<<return_type<<endl;}
    if(!classtable->inherits(t, return_type)){
        cerr<<"expr in method has bad type"<<endl;
    }
    
    otable->exitscope();
    if(semant_debug){cerr<<"completed method semant for: "<<name<<endl;}
}

void attr_class::semant(){
    if(semant_debug){cerr<<"begin semant in attr_class"<<endl;}
    //call semant on the expression
    init->semant();
    
    //verify that the expression type inherits the declared type
    Symbol t = init->get_type();
    if(semant_debug){cerr<<"checking ainherits for: "<<t<<" and "<<type_decl<<endl;}
    if(!classtable->inherits(t, type_decl)){
        cerr<<"attribute type mismatch"<<endl;
    }
    if(semant_debug){cerr<<"completed attr semant for: "<<name<<endl;}
}

void class__class::semant(){
    if(semant_debug){cerr<<"begin semant in class__class"<<endl;}
    for(int i = features->first(); features->more(i); i = features->next(i)) {
        features->nth(i)->semant();
    }
    if(semant_debug){cerr<<"completed class semant for: "<<name<<endl;}
}

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
void program_class::semant(){
    initialize_constants();
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
        
        //if any error cannot be dealt with, move on to the next class
        for(int i = classes->first(); classes->more(i); i = classes->next(i)) {
            semant_class = classes->nth(i);
            try{
                semant_class->semant();
            }catch(std::string error_msg){
                classtable->semant_error(semant_class);
                cerr << error_msg << endl;
            }
        }
    }catch(std::string error_msg){
        classtable->semant_error();
        cerr << error_msg << endl;
    }

    if (classtable->errors()) {
	    cerr << "Compilation halted due to static semantic errors." << endl;
	    //exit(1);
    }
}


