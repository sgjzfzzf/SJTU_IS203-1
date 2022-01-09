#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream &error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;

unsigned int isInLoop = 0;
std::map<Symbol, CallDecl> callMap;

///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////

static ostream &semant_error()
{
    semant_errors++;
    return error_stream;
}

static ostream &semant_error(tree_node *t)
{
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream &internal_error(int lineno)
{
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
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
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print;

bool isValidCallName(Symbol type)
{
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type)
{
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void)
{
    // 4 basic types and Void type
    Bool = idtable.add_string("Bool");
    Int = idtable.add_string("Int");
    String = idtable.add_string("String");
    Float = idtable.add_string("Float");
    Void = idtable.add_string("Void");
    // Main function
    Main = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic
    analysis in a recursive way.
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2)
{
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls)
{
    for (int i = decls->first(); decls->more(i); i = decls->next(i))
    {
        Decl decl = decls->nth(i);
        if (decl->isCallDecl())
        {
            Symbol name = decl->getName();
            Symbol type = decl->getType();
            if (!isValidCallName(name))
            {
                semant_error(decl) << "The name of function isn't valid.\n";
            }
            else if (name == Main)
            {
                callMap.insert(std::make_pair(name, CallDecl(decl)));
            }
            else if (callMap.find(name) != callMap.end())
            {
                semant_error(decl) << "This function has already been defined.\n";
            }
            else
            {
                callMap.insert(std::make_pair(name, CallDecl(decl)));
            }
        }
    }
}

static void install_globalVars(Decls decls)
{
    for (int i = decls->first(); decls->more(i); i = decls->next(i))
    {
        Decl decl = decls->nth(i);
        if (!decl->isCallDecl())
        {
            Symbol name = decl->getName();
            Symbol type = decl->getType();
            if (!isValidTypeName(name))
            {
                semant_error(decl) << "The name of variable isn't valid.\n";
            }
            else if (objectEnv.lookup(name) != NULL)
            {
                semant_error(decl) << "This variable has already been define.\n";
            }
            else if (!isValidTypeName(type))
            {
                semant_error(decl) << "This variable doesn't have a correct type.\n";
            }
            else
            {
                objectEnv.addid(name, new Symbol(type));
            }
        }
    }
}

static void check_calls(Decls decls)
{
    for (int i = decls->first(); decls->more(i); i = decls->next(i))
    {
        Decl decl = decls->nth(i);
        if (decl->isCallDecl())
        {
            objectEnv.addid(decl->getName(), new Symbol(decl->getType()));
            decl->check();
        }
    }
}

static void check_main()
{
    std::map<Symbol, CallDecl>::iterator it = callMap.find(Main);
    if (it == callMap.end())
    {
        semant_error() << "The main function doesn't exsits.\n";
    }
    else
    {
        CallDecl mainDecl = it->second;
        if (!sameType(mainDecl->getType(), Void))
        {
            semant_error(mainDecl) << "Main function should have return type Void.\n";
        }
        if (mainDecl->getVariables()->len() > 0)
        {
            semant_error(mainDecl) << "The main function has parameters.\n";
        }
    }
}

void VariableDecl_class::check()
{
    Symbol name = getName();
    Symbol type = getType();
    bool isNotExisted = true;
    bool isNotValidType = true;
    if (objectEnv.probe(name) != NULL)
    {
        isNotExisted = false;
        semant_error(this) << "This variable has been defined before.\n";
    }
    if (!isValidTypeName(type))
    {
        isNotValidType = false;
        semant_error(this) << "This variable doesn't have a correct type.\n";
    }
    if (isNotExisted && isNotValidType)
    {
        objectEnv.addid(name, new Symbol(type));
    }
}

void CallDecl_class::check()
{
    bool isReturnExisted = false;
    objectEnv.enterscope();
    if (!sameType(*objectEnv.lookup(name), returnType))
    {
        semant_error(this) << "This function's return type doesn't match its declaration's.\n";
    }
    if (paras->len() > 6)
    {
        semant_error(this) << "This function has more than 6 parameters.\n";
    }
    for (int i = paras->first(); paras->more(i); i = paras->next(i))
    {
        Variable para = paras->nth(i);
        if (!isValidTypeName(para->getName()))
        {
            semant_error(this) << "One of the function's parameters has an incorrect type.\n";
        }
        else
        {
            objectEnv.addid(para->getName(), new Symbol(para->getType()));
        }
    }
    StmtBlock body = getBody();
    Stmts bodyStmts = body->getStmts();
    body->check(getType());
    for (int i = bodyStmts->first(); bodyStmts->more(i); i = bodyStmts->next(i))
    {
        Stmt stmt = bodyStmts->nth(i);
        if (stmt->isReturnStmt())
        {
            isReturnExisted = true;
            break;
        }
    }
    if (!isReturnExisted)
    {
        semant_error(this) << "Function main must have an overall return statement.\n";
    }
    objectEnv.exitscope();
}

void StmtBlock_class::check(Symbol type)
{
    objectEnv.enterscope();
    for (int i = vars->first(); vars->more(i); i = vars->next(i))
    {
        VariableDecl var = vars->nth(i);
        var->check();
    }
    for (int i = stmts->first(); stmts->more(i); i = stmts->next(i))
    {
        Stmt stmt = stmts->nth(i);
        stmt->check(type);
    }
    objectEnv.exitscope();
}

void IfStmt_class::check(Symbol type)
{
    if (!sameType(condition->checkType(), Bool))
    {
        semant_error(this) << "This \"if\" statement's condition has a wrong type.\n";
    }
    thenexpr->check(type);
    elseexpr->check(type);
}

void WhileStmt_class::check(Symbol type)
{
    if (!sameType(condition->checkType(), Bool))
    {
        semant_error(this) << "This \"while\" statement's condition has a wrong type.\n";
    }
    ++isInLoop;
    body->check(type);
    --isInLoop;
}

void ForStmt_class::check(Symbol type)
{
    if (!initexpr->is_empty_Expr())
    {
        initexpr->checkType();
    }
    if (!condition->is_empty_Expr())
    {
        condition->checkType();
    }
    if (!loopact->is_empty_Expr())
    {
        loopact->checkType();
    }
    ++isInLoop;
    body->check(type);
    --isInLoop;
}

void ReturnStmt_class::check(Symbol type)
{
    if ((value->is_empty_Expr() && !sameType(type, Void)) || !sameType(value->checkType(), type))
    {
        semant_error(this) << "Returns " << value->getType() << " , but need " << type << "\n";
    }
}

void ContinueStmt_class::check(Symbol type)
{
    if (!isInLoop)
    {
        semant_error(this) << "This continue statement isn't in a loop.\n";
    }
}

void BreakStmt_class::check(Symbol type)
{
    if (!isInLoop)
    {
        semant_error(this) << "break must be used in a loop sentence.\n";
    }
}

Symbol Call_class::checkType()
{
    std::map<Symbol, CallDecl>::iterator it = callMap.find(name);
    if (it == callMap.end())
    {
        semant_error(this) << "This function hasn't been defined.";
        setType(Void);
    }
    else if (name->get_string() == print->get_string())
    {
        if (actuals->len())
        {
            semant_error(this) << "The printf function doesn't have parameters.\n";
        }
        if (!sameType(actuals->nth(actuals->first())->getType(), String))
        {
            semant_error(this) << "The first paramter of the printf function isn't String.\n";
        }
        for (int i = actuals->first(); actuals->more(i); i = actuals->next(i))
        {
            actuals->nth(i)->checkType();
        }
        setType(Void);
    }
    else
    {
        CallDecl callDecl = it->second;
        Variables variables = callDecl->getVariables();
        int i = 0;
        int j = 0;
        int para_index = 1;
        for (; variables->more(i) && actuals->more(j); i = variables->next(i), j = actuals->next(j))
        {
            Actual actual = actuals->nth(i);
            if (!sameType(variables->nth(i)->getType(), actual->checkType()))
            {
                semant_error(this) << "Function loop, the " << para_index << " parameter should be " << variables->nth(i)->getType() << " but provided a " << actual->getType() << ".\n";
                return callDecl->getType();
            }
            ++para_index;
        }
        if (variables->more(i) || actuals->more(j))
        {
            semant_error(this) << "The number of parameters don't match the declaration.\n";
        }
        setType(callDecl->getType());
    }
    return type;
}

Symbol Actual_class::checkType()
{
    setType(expr->checkType());
    return type;
}

Symbol Assign_class::checkType()
{
    Symbol valueType = value->checkType();
    Symbol *type = objectEnv.lookup(lvalue);
    if (!type)
    {
        semant_error(this) << "This symbol hasn't been defined.\n";
        setType(Void);
    }
    else if ((sameType(*type, Float) && sameType(valueType, Int)) || (sameType(*type, Int) && sameType(valueType, Float)))
    {
        setType(*type);
    }
    else if (sameType(*type, valueType))
    {
        setType(*type);
    }
    else
    {
        semant_error(this) << "Types of the left value and the right value don't match.\n";
        setType(Void);
    }
    return *type;
}

Symbol Add_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Int) && (sameType(e2Type, Int)))
    {
        setType(Int);
    }
    else if ((sameType(e1Type, Int) && (sameType(e2Type, Float))) || (sameType(e1Type, Float) && (sameType(e2Type, Int))) || (sameType(e1Type, Float) && (sameType(e2Type, Float))))
    {
        setType(Float);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this addition expression are wrong.\n";
    }
    return type;
}

Symbol Minus_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Int) && (sameType(e2Type, Int)))
    {
        setType(Int);
    }
    else if ((sameType(e1Type, Int) && (sameType(e2Type, Float))) || (sameType(e1Type, Float) && (sameType(e2Type, Int))) || (sameType(e1Type, Float) && (sameType(e2Type, Float))))
    {
        setType(Float);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this substraction expression are wrong.\n";
    }
    return type;
}

Symbol Multi_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Int) && (sameType(e2Type, Int)))
    {
        setType(Int);
    }
    else if ((sameType(e1Type, Int) && (sameType(e2Type, Float))) || (sameType(e1Type, Float) && (sameType(e2Type, Int))) || (sameType(e1Type, Float) && (sameType(e2Type, Float))))
    {
        setType(Float);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this multiplication expression are wrong.\n";
    }
    return type;
}

Symbol Divide_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Int) && (sameType(e2Type, Int)))
    {
        setType(Int);
    }
    else if ((sameType(e1Type, Int) && (sameType(e2Type, Float))) || (sameType(e1Type, Float) && (sameType(e2Type, Int))) || (sameType(e1Type, Float) && (sameType(e2Type, Float))))
    {
        setType(Float);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this division expression are wrong.\n";
    }
    return type;
}

Symbol Mod_class::checkType()
{
    if (sameType(e1->checkType(), Int) && sameType(e2->checkType(), Int))
    {
        setType(Int);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this mod expression are wrong.\n";
    }
    return type;
}

Symbol Neg_class::checkType()
{
    Symbol tmpType = e1->checkType();
    if (sameType(tmpType, Int) || sameType(tmpType, Float))
    {
        setType(tmpType);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The type of the value in this negative expression is wrong.\n";
    }
    return type;
}

Symbol Lt_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if ((sameType(e1Type, Int) || sameType(e1Type, Float)) && (sameType(e2Type, Int) || sameType(e2Type, Float)))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this lt expression are wrong.\n";
    }
    return type;
}

Symbol Le_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if ((sameType(e1Type, Int) || sameType(e1Type, Float)) && (sameType(e2Type, Int) || sameType(e2Type, Float)))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this le expression are wrong.\n";
    }
    return type;
}

Symbol Equ_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if ((sameType(e1Type, Int) || sameType(e1Type, Float)) && (sameType(e2Type, Int) || sameType(e2Type, Float)))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this equ expression are wrong.\n";
    }
    return type;
}

Symbol Neq_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (((sameType(e1Type, Int) || sameType(e1Type, Float)) && (sameType(e2Type, Int) || sameType(e2Type, Float))) || (sameType(e1Type, Bool) && sameType(e2Type, Bool)))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this neq expression are wrong.\n";
    }
    return type;
}

Symbol Ge_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if ((sameType(e1Type, Int) || sameType(e1Type, Float)) && (sameType(e2Type, Int) || sameType(e2Type, Float)))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this ge expression are wrong.\n";
    }
    return type;
}

Symbol Gt_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if ((sameType(e1Type, Int) || sameType(e1Type, Float)) && (sameType(e2Type, Int) || sameType(e2Type, Float)))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this gt expression are wrong.\n";
    }
    return type;
}

Symbol And_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Bool) && sameType(e2Type, Bool))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this and expression are wrong.\n";
    }
    return type;
}

Symbol Or_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Bool) && sameType(e2Type, Bool))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this or expression are wrong.\n";
    }
    return type;
}

Symbol Xor_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Bool) && sameType(e2Type, Bool))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this xor expression are wrong.\n";
    }
    return type;
}

Symbol Not_class::checkType()
{
    Symbol tmpType = e1->checkType();
    if (sameType(tmpType, Bool))
    {
        setType(Bool);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this not expression are wrong.\n";
    }
    return type;
}

Symbol Bitand_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Int) && sameType(e2Type, Int))
    {
        setType(Int);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this bitand expression are wrong.\n";
    }
    return type;
}

Symbol Bitor_class::checkType()
{
    Symbol e1Type = e1->checkType();
    Symbol e2Type = e2->checkType();
    if (sameType(e1Type, Int) && sameType(e2Type, Int))
    {
        setType(Int);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this bitor expression are wrong.\n";
    }
    return type;
}

Symbol Bitnot_class::checkType()
{
    Symbol tmpType = e1->checkType();
    if (sameType(tmpType, Int))
    {
        setType(Int);
    }
    else
    {
        setType(Void);
        semant_error(this) << "The types of two values of this bitnot expression are wrong.\n";
    }
    return type;
}

Symbol Const_int_class::checkType()
{
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType()
{
    setType(String);
    return type;
}

Symbol Const_float_class::checkType()
{
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType()
{
    setType(Bool);
    return type;
}

Symbol Object_class::checkType()
{
    bool flag = false;
    Symbol *tmpType = objectEnv.lookup(var);
    if (tmpType)
    {
        setType(*tmpType);
    }
    else
    {
        setType(Void);
        semant_error(this) << "object " << var <<  " has not been defined.\n";
    }
    return type;
}

Symbol No_expr_class::checkType()
{
    setType(Void);
    return type;
}

void Program_class::semant()
{
    objectEnv.enterscope();
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    objectEnv.exitscope();

    if (semant_errors > 0)
    {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}
