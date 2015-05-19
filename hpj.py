# hpj.py
# Simple Python to Javascript translator with an emphasis on readability of generated code.
# This code is based on Niall McCarroll's py2js code. It is a very
# basic python to javascript intereprter, with an emphasis on
# readability of javascript code.
#
# Usage: python hpj.py <file.py>
# generates: hyj.js and file.js
#
# The MIT License
#
# Copyright (c) 2008 - 2009 Niall McCarroll
# Copyright (c) 2013 - 2015 Hiep Huu Nguyen
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
#
#
#
# some of this code is from the pyjamas project
# Copyright 2006 James Tauber and contributors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# classes to model a parse tree that is a simplified equivalent to python's ast
# Expression related
import copy, re
import _ast
import codecs
import sys, os, time
from types import IntType, ListType, StringType, TupleType, DictType

class Scope(object):

    def __init__(self,name):
        self.scopename = name
        self.globals = set()
        self.yieldScope = False
        self.yieldState = 0
        self.lineno = -1

    def addGlobal(self,name):
        self.globals.add(name)

    def isGlobal(self,name):
        return name in self.globals

    def printscope(self):
        return ('scope',self.scopename,self.globals)

    def JSYieldGuard(self, yieldState=0):
        yieldState += self.yieldState
        return 'if (_yieldobj._yieldState <= ' + str(yieldState) + ')'

class ScopeManager:
    def __init__(self):
        self.scope = []
        self.yieldState = 0
        self.inYieldFn = False

    def JSYieldGuard(self, stmtObj):
        yieldScope = False
        for scope in self.scope:
            if scope.yieldScope:
                yieldScope = True
                break
        if yieldScope:
            return stmtObj.JSYieldGuard(self.yieldState)
        return stmt

    def incrYieldState(self):
        self.yieldState += 1

    def pushScope(self,scope):
        return self.scope.append(scope)

    def popScope(self):
        if len(self.scope) != 0:
            self.scope.pop()

    def getInnerScope(self):
        if not self.scope:
            return None
        return self.scope[-1]

    def isLocal(self,name):
        return self.getInnerScope().isGlobal(name)

    def isGlobal(self,name, scopeType=None):
        #if isinstance(self.getInnerScope(),Module):
        #    return True
        for scope in self.scope[:-1]:
            if scopeType and isinstance(scope, scopeType) and scope.isGlobal(name):
                return True
            if scopeType and isinstance(scope, scopeType) and not scope.isGlobal(name):
                return False
            if not scopeType and scope.isGlobal(name):
                return True
        return False

    def getNamespace(self,name):
        namespaces = []
        seen = False
        for i in xrange(len(self.scope)-1, -1, -1):
            scope = self.scope[i]
            if seen:
                if  isinstance(scope, ClassDefinitionStatement):  namespaces.append(scope.cname)
                if  isinstance(scope, Module):  namespaces.append(scope.name)
            elif scope.isGlobal(name):
                if not isinstance(scope, ClassDefinitionStatement) and not isinstance(scope, Module):
                    return ""
                elif isinstance(scope, ClassDefinitionStatement):
                    seen = True
                    namespaces.append(scope.cname)
                elif isinstance(scope, Module):
                    seen = True
                    namespaces.append(scope.name)
            elif scope.scopename==name:
                seen=True
        if not seen:
            return ""
        namespaces.reverse()
        return ".".join(namespaces)

    def hasOuterScope(self, scopeType):
        for i in xrange(len(self.scope)-1, -1, -1):
            scope = self.scope[i]
            if isinstance(scope, scopeType):            
                return True
        return False

    def setYieldScope(self):
        for i in xrange(len(self.scope)-1, -1, -1):
            scope = self.scope[i]
            scope.yieldState += 1
            scope.yieldScope = True
            if isinstance(scope, FunctionDefinitionStatement):
                break

    def addGlobal(self,name):
        if not self.getInnerScope():
            return True
        self.getInnerScope().addGlobal(name)



class Expr(Scope):

    def __init__(self, name=""):
        Scope.__init__(self,name)

    def walk(self,walker):
        walker.begin(self)
        walker.end(self)

# Sub-classes of Expr
    
class AttributeLookup(Expr):

    def __init__(self,obj,attr):
        self.obj = obj
        self.attr = attr
        Expr.__init__(self)

    def __repr__(self):
        return str(('attribute',self.obj,self.attr))

    def walk(self,walker):
        walker.begin(self)
        self.obj.walk(walker)
        walker.end(self)

class BinaryOp(Expr):

    def __init__(self,op,left,right):
        self.op = op
        self.left = left
        self.right = right
        Expr.__init__(self)

    def __repr__(self):
        return str(('binaryop',self.op,self.left,self.right))

    def walk(self,walker):
        walker.begin(self)
        self.left.walk(walker)
        self.right.walk(walker)
        walker.end(self)

class DictionaryValue(Expr):

    def __init__(self,keyvalues):
        self.keyvalues = keyvalues
        Expr.__init__(self)

    def __repr__(self):
        return str(('keyvalues',self.keyvalues))

    def walk(self,walker):
        walker.begin(self)
        for (k,v) in self.keyvalues:
            if k:
                k.walk(walker)
            if v:
                v.walk(walker)
        walker.end(self)

class FunctionCall(Expr):

    def __init__(self,fname,args,kwargs):
        self.fname = fname
        self.args = args
        self.kwargs = kwargs
        Expr.__init__(self)

    def __repr__(self):
        return str(('fcall',self.fname,self.args,self.kwargs))

    def walk(self,walker):
        walker.begin(self)
        for arg in self.args:
            arg.walk(walker)
        # fixme kwargs?
        walker.end(self)

class Lambda(Expr):

    def __init__(self,args,body):
        self.args = args
        self.body = body
        Expr.__init__(self,"lambda")

    def __repr__(self):
        return str(('lambda',self.args,self.body))

    def walk(self,walker):
        walker.begin(self)
        for arg in self.args:
            arg.walk(walker)
        self.body.walk(walker)
        walker.end(self)

class ListValue(Expr):

    def __init__(self,elements):
        self.elements = elements
        Expr.__init__(self)

    def __repr__(self):
        return str(('listvalue',self.elements))

    def walk(self,walker):
        walker.begin(self)
        for elt in self.elements:
            elt.walk(walker)
        walker.end(self)

class ListComprehension(Expr):

    def __init__(self,expr,generators):
        self.expr = expr
        self.generators = generators
        Expr.__init__(self)

    def __repr__(self):
        return str(('listcomp',self.expr,self.generators))

    def walk(self,walker):
        walker.begin(self)
        self.expr.walk(walker)
        for generator in self.generators:
            generator.walk(walker)
        walker.end(self)

class ListComprehensionGenerator(Expr):

    def __init__(self,target,itr,cond):
        self.target = target
        self.itr = itr
        self.cond = cond
        Expr.__init__(self)

    def __repr__(self):
        return str(('listcomp_gen',self.target,self.itr,self.conds))

    def walk(self,walker):
        walker.begin(self)
        self.target.walk(walker)
        self.itr.walk(walker)
        for generator in self.conds:
            generator.walk(walker)
        walker.end(self)

class Literal(Expr):

    def __init__(self,value):
        self.value = value
        Expr.__init__(self)

    def __repr__(self):
        return str(('literal',self.value))

class MethodCall(FunctionCall):

    def __init__(self,target,fname,args,kwargs):
        self.target = target
        FunctionCall.__init__(self,fname,args,kwargs)

    def __repr__(self):
        return str(('mcall',self.target,FunctionCall.__repr__(self)))

    def walk(self,walker):
        walker.begin(self)
        self.target.walk(walker)
        for arg in self.args:
            arg.walk(walker)
        walker.end(self)

class SliceOp(Expr):
    
    def __init__(self,target,slicing):
        self.target = target
        self.lwb = slicing[0]
        self.upb = slicing[1]
        self.step = slicing[2]

    def __repr__(self):
        return str(('slice',self.lwb,self.upb,self.step))

    def walk(self,walker):
        if self.lwb:
            self.lwb.walk(walker)
        if self.upb:
            self.upb.walk(walker)
        if self.step:
            self.step.walk(walker)
        walker.end(self)

class UniOp(Expr):

    def __init__(self,op,arg):
        self.op = op
        self.arg = arg
        Expr.__init__(self)

    def __repr__(self):
        return str(('unaryop',self.op,self.arg))

    def walk(self,walker):
        walker.begin(self)
        self.arg.walk(walker)
        walker.end(self)

class VarName(Expr):

    def __init__(self,varname):
        self.varname = pj_var.get(varname,varname)
        Expr.__init__(self)

    def __repr__(self):
        return str(('var',self.varname))

    def __repr__(self):
        return str(('name',self.varname))

    def walk(self,walker):
        walker.begin(self)
        walker.end(self)

# Statement related


class Statement(Scope):

    def __init__(self, name="statement"):
        Scope.__init__(self,name)

# Statement sub-classes
       
class AssignmentStatement(Statement):
    
    def __init__(self,target,expr):
        self.target = target
        self.expr = expr
        Statement.__init__(self)

    def __repr__(self):
        return str(('assign',self.target,self.expr))

class AugmentedAssignmentStatement(Statement):
    
    def __init__(self,target,op,expr):
        self.target = target
        self.op = op
        self.expr = expr
        Statement.__init__(self)

    def __repr__(self):
        return str(('augmented_assign',self.target,self.op,self.expr))

class BreakStatement(Statement):
    
    def __init__(self):
        Statement.__init__(self)

    def __repr__(self):
        return str(('break'))

class ClassDefinitionStatement(Statement):

    registered = {}

    def __init__(self,cname,module):
        self.cname = pj_var.get(cname,cname)
        self.module = module
        self.parent_class = None
        Statement.__init__(self,"class:"+cname)

    def configure(self,bases,constructor,memberfns,staticvars,innerclasses):
        self.bases = bases
        self.constructor = constructor
        self.mfns = memberfns
        self.staticmembervars = staticvars
        self.innerclasses = innerclasses
        ClassDefinitionStatement.register(self)

    def getClassNamespace(self):
        if self.parent_class:
            namespace = self.parent_class.getClassNamespace()
        elif self.module:
            namespace = self.module.name # space
        else:
            namespace = ""
        if namespace != "":
            namespace += "."
        namespace += self.cname
        return namespace

    def setParentClass(self,parent):
        self.parent_class = parent

    def __repr__(self):
        return str(('cdef',self.cname,self.module,self.parent_class,self.bases,self.constructor,self.mfns,self.staticmembervars, self.innerclasses))

    @staticmethod 
    def register(cdef):
        ClassDefinitionStatement.registered[cdef.cname] = cdef

    @staticmethod
    def isclassname(name):
        return name in ClassDefinitionStatement.registered

    @staticmethod
    def getclass(name):
        if name in ClassDefinitionStatement.registered:
            return ClassDefinitionStatement.registered[name]
        else:
            return None

    # method resolution order utilities

    @staticmethod
    def getbases(C):
        klass = ClassDefinitionStatement.getclass(C)
        if klass != None:
            return klass.bases[:]
        else:
            return []

    # methods merge,mro and compute_mro based on code and description
    # of the method resolution order here:
    # http://www.python.org/download/releases/2.3/mro/
    @staticmethod
    def merge(seqs):
        res = []; i=0
        while 1:
          nonemptyseqs=[seq for seq in seqs if seq]
          if not nonemptyseqs: return res
          i+=1 
          for seq in nonemptyseqs: # find merge candidates among seq heads
              cand = seq[0] 
              nothead=[s for s in nonemptyseqs if cand in s[1:]]
              if nothead: cand=None #reject candidate
              else: break
          if not cand: raise "Inconsistent hierarchy"
          res.append(cand)
          for seq in nonemptyseqs: # remove cand
              if seq[0] == cand: del seq[0]

    @staticmethod
    def mro(C):
        "Compute the class precedence list (mro) according to C3"
        return ClassDefinitionStatement.merge([[C]]
                +map(ClassDefinitionStatement.mro,ClassDefinitionStatement.getbases(C))
                +[list(ClassDefinitionStatement.getbases(C))])

    @staticmethod
    def compute_mro(cname):
        namelist = ClassDefinitionStatement.mro(cname)
        return map(ClassDefinitionStatement.getclass,namelist)

    def memberfns(self,forsuper=False):
        fns = []
        for f in self.mfns:
            fname = f.fname
            if fname not in fns:
                fns.append([fname, self.getClassNamespace(),f])
        return fns

    def oldmemberfns(self,forsuper=False):
        classes = ClassDefinitionStatement.compute_mro(self.cname)
        fns = {}
        for clas in classes:
            # clas may be None for the base class (object or other built in class)
            if clas:
                cname = clas.cname
                if forsuper and cname == self.cname:
                    continue
                cfns = clas.mfns
                if forsuper and clas.constructor:
                    cfns.append(clas.constructor)
                for f in cfns:
                    fname = f.fname
                    if fname not in fns:
                        fns[fname] = (clas.getClassNamespace(),f)
                
        return fns

    def innerclasslist(self):
        classes = ClassDefinitionStatement.compute_mro(self.cname)
        innerclasses = []
        for clas in classes:
            if clas:
                for innerclass in clas.innerclasses:
                    innerclasses.append((innerclass,clas.getClassNamespace()))
        return innerclasses

class ContinueStatement(Statement):
    
    def __init__(self):
        Statement.__init__(self)

    def __repr__(self):
        return str(('continue'))

class DeleteStatement(Statement):

    def __init__(self,target):
        Statement.__init__(self)
        self.target = target

    def __repr__(self):
        return str(("delete",self.target))

class DeclareStatement(Statement):

    def __init__(self,declarevars):
        self.declarevars = declarevars
        Statement.__init__(self)

    def __repr__(self):
        return str(('declare',self.declarevars))        

class EmptyStatement(Statement):
    
    def __init__(self):
        Statement.__init__(self)

    def __repr__(self):
        return str(('pass'))

class ExceptionHandlerStatement(Statement):

    def __init__(self,etype,ename,ebody):
        self.etype = etype
        self.ename = ename
        self.ebody = ebody
        Statement.__init__(self, "except")
        
    def __repr__(self):
        return str(('except',self.etype,self.ename,self.ebody))
  
class ExpressionStatement(Statement):

    def __init__(self,expr):
        self.expr = pj_var.get(expr,expr)
        Statement.__init__(self)

    def __repr__(self):
        return str(('expression',self.expr))

class ForInStatement(Statement):
    
    def __init__(self,target,container,block):
        self.target = pj_var.get(target,target)
        self.container = container
        self.block = block
        Statement.__init__(self, "forIn")

    def __repr__(self):
        return str(('for in',self.target,self.container,self.block))

class ForStatement(Statement):
    
    def __init__(self,varname,lwb,upb,step,block):
        self.varname = pj_var.get(varname,varname)
        self.lwb = lwb
        self.upb = upb
        self.step = step
        self.block = block
        Statement.__init__(self, "for")

    def __repr__(self):
        return str(('for',self.varname,self.lwb,self.upb,self.step,self.block))

class FunctionDefinitionStatement(Statement):

    def __init__(self,fname):
        self.fname = pj_var.get(fname,fname)
        Statement.__init__(self,"function:"+fname)


    def configure(self,decorators,argnames,argdefaults,vararg,kwarg,block):
        self.decorators = decorators
        self.argnames = argnames
        self.argdefaults = argdefaults
        self.vararg = vararg
        self.kwarg = kwarg
        self.block = block

    def __repr__(self):
        return str(('fdef',self.fname,self.decorators,self.argnames,self.argdefaults,self.block))

class GlobalStatement(Statement):

    def __init__(self,varname):
        self.varname = varname
        Statement.__init__(self)

    def __repr__(self):
        return str(('global',self.varname))
        
class IfStatement(Statement):
    
    def __init__(self,tests,elseblock):
        self.tests = tests
        self.elseblock = elseblock
        Statement.__init__(self)

    def __repr__(self):
        return str(('if',self.tests,self.elseblock))

class PrintStatement(Statement):
    
    def __init__(self,values):
        self.values = values
        Statement.__init__(self)

    def __repr__(self):
        return str(('print',self.values))

class RaiseStatement(Statement):

    def __init__(self,rtype,robj):
        self.rtype = rtype
        self.robj = robj
        Statement.__init__(self)

    def __repr__(self):
        return str(('raise',self.rtype,self.robj))

class ReturnStatement(Statement):
    
    def __init__(self,returnvalue):
        self.value = returnvalue # may be None
        Statement.__init__(self)

    def __repr__(self):
        return str(('return',self.value))
    
class YieldStatement(Statement):
    
    def __init__(self,returnvalue):
        self.value = returnvalue # may be None
        Statement.__init__(self)

    def __repr__(self):
        return str(('yield',self.value))

    
class TryStatement(Statement):

    def __init__(self,body,handlers,final):
        self.body = body
        self.handlers = handlers
        self.final = final
        Statement.__init__(self, "try")

    def __repr__(self):
        return str(('try',self.body,self.handlers,self.final))

class Verbatim(Statement):

    def __init__(self,text,exp=False):
        self.text = text
        self.exp=exp
        Statement.__init__(self)

    def __repr__(self):
        return str(('verbatim',self.text))

class WhileStatement(Statement):

    def __init__(self,cond,block):
        self.cond = cond
        self.block = block
        Statement.__init__(self)

    def __repr__(self):
        return str(('while',self.cond,self.block))

# Block contains a group of statements

class Block(Scope):

    def __init__(self,statements):
        self.statements = statements
        Scope.__init__(self,"block")

    def __repr__(self):
        return str(('block',self.statements))

# Module describes a python module

class Module(Scope):
    def __init__(self,name,path,namespace):
        self.name = pj_var.get(name,name)
        self.path = path
        self.namespace = namespace
        self.module_mountpoints = {}
        self.class_mountpoints = {}
        self.aliases = []
        Scope.__init__(self,"module:"+self.name)
        self.code = None
        self.parent_module = None

    def configure(self,code):
        self.code = code
        self.parent_module = None

    def setParentModule(self,parent_module):
        self.parent_module = parent_module

    def addModuleMountPoint(self,name,mountpoint):
        self.module_mountpoints[name] = mountpoint

    def addClassMountPoint(self,name,mountpoint):
        self.class_mountpoints[name] = mountpoint


    def getMountPoint(self,name):
        if name in self.module_mountpoints:
            return self.module_mountpoints[name]
        if name in self.class_mountpoints:
            return self.class_mountpoints[name]
        return None

    def getClassMountPoint(self,name):
        if name in self.class_mountpoints:
            return self.class_mountpoints[name]
        return None

    def applyAliases(self,name):
        for (originalname,namealias) in self.aliases:
           if name == originalname:
               return namealias
        return name

    def __repr__(self):
        return str(('module',self.name,self.aliases,self.code))

# Walker utilities

class VarNameWalker(object):

    def __init__(self):
        self.varnames = []

    def getVarNames(self):
        return self.varnames

    def begin(self,node):
        if isinstance(node,VarName):
            if not node.varname in self.varnames:
                self.varnames.append(node.varname)
                node.first = True    

    def end(self,node):
        pass

# Scope utilities

def printscope(scope):
    for s in scope:
        print(str(s))

pj_modules = {}

pj_var = {
    "math.e":"Math.E", #FIXME
    "math.pi":"Math.PI", #FIXME
    "IntType":"Number",
    "LongType":"Number",
    "FloatType":"Number",
    "StringType":"String",
    "ListType":"Array",
    "list":"Array",
    "tuple":"Array",
    "TupleType":"Array",
    "DictType":"Object",
    "BooleanType":"Boolean",
    "new":"new_",
    "delete":"delete_",
    "this":"this_",
#    "null":"null_",
    "function":"function_",
    "default":"default_",
    "typeof":"typeof_",
    "undefined":"undefined_",
    "var":"var_",
    "arguments":"arguments_",
    "instanceof":"instanceof_",
    }


# binary operators

binaryOps = { 
    'and'       : '&&', 
    'or'        : '||', 
    '=='        : '===', 
    '!='        : '!==', 
    '**'        : 'Math.pow(%1,%2)',
    '[]'        : '%1[%2]',
    '<'         : '<',
    '<='        : '<=',
    '>'         : '>',
    '>='        : '>=',
    '<>'        : '!==',
    'is'        : '===',
    'is not'    : '!==',
    'in'        : ('$pj.in(%1,%2)',['$pj.in']),
    'not in'    : ('!($pj.in(%1,%2))',['$pj.in']),
    '|'         : '|',
    '^'         : '^',
    '&'         : '&',
    '%'         : '%',
    '//'        : 'Math.floor(%1/%2)',
    '+'         : '+',
    '-'         : '-',
    '*'         : '*',
    '/'         : '/',
    '>>'        : '>>',
    '<<'        : '<<'
    }

# unary operators

unaryOps = { 
    'not'       : '!', 
    '-'         : '-',
    '+'         : '+',
    '~'         : '~'
}

# augmented assignment operators (always supply placeholders)

assignOps = {
    '+='        : '%1 += %2',
    '-='        : '%1 -= %2',
    '*='        : '%1 *= %2',
    '/='        : '%1 /= %2',
    '//='       : '%1 = Math.floor(%1/%2)',
    '%='        : '%1 %= %2',
    '>>='       : '%1 >>= %2',
    '<<='       : '%1 <<= %2',
    '**='       : '%1 = Math.pow(%1,%2)',
    '&='        : '%1 &= %2',
    '|='        : '%1 |= %2',
    '^='        : '%1 ^= %2'
}

#
# map between python builtins and javascript operators, functions or whatever
#
# where python and javascript builtin are the same, no need to include the mapping in this file
#
# for keys use the function name or "." plus the method name
# 
# to provide different mappings based on the number of arguments 
# supplied to the function/method, add the suffix .<#args> to the key.  
# 
# For example:
#   "spam.1" : js_eggs"   ... maps python function spam to javascript function js_eggs when exactly 
#                             1 argument is supplied   
#   "spam" : "js_spam"    ... maps python function spam to javascript function js_spam
#   
# JSMap is loaded from the different modules imported by a program and inserted into the mappedFuncs table.

pj_lib = """



var $pj = $pj || {};

$pj.main_module = "";

$pj.loaded_modules = $pj.loaded_modules || [];

$pj.print = function(str) {
    if (console) { 
      console.log(str); 
    } else {
      document.write(str + "<BR>");
    }
}

$pj.items = function(obj) {
    if (obj.items) { return obj.items(); }
    var items = [];
    for (var key in obj) {
      items.push([key, obj[key]]);
    }
    return items;
};


$pj.values = function(obj) {
    if (obj.values) { return obj.values(); }
    var values = [];
    for (var k in obj)
      values.push(obj[k]);
    return values;
};

$pj.copy = function(obj) {
    if ((!obj) || (obj instanceof String) || (typeof(obj)=== 'string') || (typeof(obj)=== 'number') || (typeof(obj)=== 'boolean') || (obj instanceof Number) || (obj instanceof Boolean)) { return obj; } 
    if (obj instanceof Date) { return new Date(obj.getTime()); }
    var newObj = ((typeof(obj) === 'array') || (obj instanceof Array)) ? [] : (obj.__new__ ? obj.__new__(undefined): {});
    for (i in obj) {
       newObj[i] = this[i];
    } 
    return newObj;
}


$pj.deepcopy = function(obj) {
    if ((!obj) || (obj instanceof String) || (typeof(obj)=== 'string') || (typeof(obj)=== 'number') || (typeof(obj)=== 'boolean') || (obj instanceof Number) || (obj instanceof Boolean)) { return obj; } 
    if (obj instanceof Date) { return new Date(obj.getTime()); }
    var newObj = ((typeof(obj) === 'array') || (obj instanceof Array)) ? [] : (obj.__new__ ? obj.__new__(undefined): {});
    for (i in obj) {
       if (obj[i] && this[i] instanceof Object) {
            newObj[i] = $pj.deepcopy(this[i]);
       } else {
            newObj[i] = this[i];
       }
    } 
    return newObj;
}

function Kwarg(dict) {
    this.dict = dict;
}
Kwarg.prototype.getDict = function() {
    return this.dict;
}


$pj.t = function(item) {
    return (((item instanceof Array)  || (typeof(item) === 'array')) ? (item.length !== 0 ? item: false) : item)
}

$pj.in = function(item,container) {
    if ((container instanceof Array) || (container instanceof String) || (typeof(container) === 'array') || (typeof(container) === 'string')) {
        return container.indexOf(item) !== -1;
    }
    return item in container;
}

$pj.len = function(container) {
    if ((container instanceof Array) || (typeof(container) === 'array')) {
            return container.length;
    }
    var i;
    var count = 0;
    for (i in container) {
        count++;
    }
    return count;
}

$pj.xrange2 = function(min,max) {
        result = [];
        var i;
        for(i=min;i<max;i++) {
            result.push(i);
        }
        return result;
}

$pj.xrange3 = function(min,max,step) {
     if (step > 0) {
        result = [];
        var i;
        for(i=min;i<max;i+=step) {
            result.push(i);
        }
        return result;
    } else {
        result = [];
        var i;
        for(i=max;i>min;i-=step) {
            result.push(i);
        }
        return result;
    }
}

$pj.replace = function(str,mat,rep) {
    if (str.replace) { return str.replace(mat,rep); } 

    var s = str;    
    var pos = s.indexOf(mat,0);
    while(pos >= 0) {
        s = "".concat(s.slice(0,pos),rep,s.slice(pos+mat.length));
        pos = s.indexOf(mat,pos+rep.length);
    }
    return s;
}

$pj.remove = function(lst,val) {
    if (lst.remove) {
	return lst.remove(val);
    }
    var idx = lst.indexOf(val);
    if (idx !== 1) lst.splice(idx,1);
    return lst;
}

$pj.sort3 = function(lst,fn,ky,rv) {
    sfn = function(a,b) {
        if (!rv) {
            return fn(ky(a),ky(b));
        } else {
            return fn(ky(b),ky(a));
        }    
    }
    lst.sort(sfn);
}


$pj.strip = function(str,chars) {
    if (str.strip) { return str.strip(chars);}
    return $pj.rstrip($pj.lstrip(str,chars),chars);
}

$pj.rstrip = function(str,chars) {
    if (str.rstrip) { return str.rstrip(chars);}

    var i = str.length-1;    
    while(i >= 0) {
        if (chars.indexOf(str.slice(i,i+1)) === -1) {
            break;
        }            
        i--;
    }
    if (i < (str.length-1)) {
        if (i < 0) {
            return "";
        }
        return str.slice(0,i+1);
    }
    return str;
}

$pj.lstrip = function(str,chars) {
    if (str.lstrip) { return str.lstrip(chars);}

    var i = 0;    
    while(i < str.length) {
        if (chars.indexOf(str.slice(i,i+1)) === -1) {
            break;
        }            
        i++;
    }
    if (i === 0) {
        return str;
    }    
    if (i === str.length) {
        return "";
    }
    return str.slice(i);
}

$pj.sum = function(list) {
    var i,total = 0;
    for(i=0;i<list.length;i++) {
        total += list[i];
    }    
    return total;
}

$pj.has_key = function(s0,s1) {
    return (s0.has_key ? s0.has_key(s1) : (s1 in s0));
}

$pj.keys = function(obj) {
    if (obj.keys) {return obj.keys();}
    var result = [];
    var k;
    for ( k in obj ) {
        result.push(k);
    }    
    return result;
}

$pj.max = function(list) {
    var result = null;
    /* FIXME should throw ValueError if list is empty */    
    for(i=0;i<list.length;i++) {
        if ((result === null) || (list[i]>result)) {
            result = list[i];
        }
    }    
    return result;
}

$pj.min = function(list) {
    var result = null;
    /* FIXME should throw ValueError if list is empty */    
    for(i=0;i<list.length;i++) {
        if ((result === null) || (list[i]<result)) {
            result = list[i];
        }
    }    
    return result;
}

$pj.map = function(fn, container) {
    if (!container) { return []; }
    var isarray = ((typeof(container) === 'array') || (container instanceof Array));
    var isstring = ((typeof(container) === 'string') || (container instanceof String));
    if (isstring && !fn) { return container; }
    if (isarray || isstring) {
        var i,result=[];
        for(i=0;i<container.length;i++) {
            if (fn) { result.push(fn(container[i])); } else { result.push(container[i]); }
        }    
        return result;
    } else {
        var generator, result = []
        if (container instanceof Generator) { generator = container; } else {generator = new Generator(container); }
        for(var val=generator.nextValue();generator.hadMore();c1=generator.nextValue()) {
            if (fn) { result.push(fn(val)); } else { result.push(val); }
        }
        return result;
   }  
  return []
}

$pj.lastEl = function(list) {
    return list[list.length-1];
}

$pj.next_token = function(str,start,match,incl,limit) {
    var pos = 0;
    var token = '';
    while(true) {
        if (start+pos > str.length) {
            return [null,(start+pos)];
        }
        var ch = str[start+pos];
        var contains = (match.indexOf(ch)===-1);
        var use = contains;
        if (!incl) {
            use = !contains;
        }
        if (use) {
            return [token,(start+pos)];
        } else {
            token += ch;
        }
        if ((limit > -1) && (token.length >= limit)) {
            return [token,(start+pos)];
        }
        pos++;
    }
    return null; 
}
        
                            
$pj.parse_format = function(format,start) {
    var pos = start+1; // skip the %

    // initialize the return object
    var fmt = new Object();
    fmt.key = null;
    fmt.code = null;
    fmt.nbytes = 0;
    fmt.useplus = false;
    fmt.ljust = false;
    fmt.space_pad = false;
    fmt.zero_pad = false;
    fmt.alternate = false;

    fmt.width = null;
    fmt.precision = null;
    
    var ch = format[pos];
    
    // parse key (optional)   
    if (ch === '(') {
        keyPos = $pj.next_token(format,pos+1,")",false,-1);
	key=keyPos[0];
	pos=keyPos[1];
        if (key === null) { return null; } 
        fmt.key = key;
        pos++; // skip the closing (
    }

    // flags
    var flags = '';
    flagsPos = $pj.next_token(format,pos,'+- 0#',true,-1);
    flags=flagsPos[0];
    pos=flagsPos[1];
    if (flags === null) { return null; }
    if (flags.indexOf('+') !== -1) { fmt.useplus = true; }
    if (flags.indexOf('-') !== -1) { fmt.ljust = true; }
    if (flags.indexOf(' ') !== -1) { fmt.space_pad = true; }       
    if (flags.indexOf('0') !== -1) { fmt.zero_pad = true; }
    if (flags.indexOf('#') !== -1) { fmt.alternate = true; }
    if (flags.useplus) {
        flags.space_pad = false;
    }

    // width
    wstrPos = $pj.next_token(format,pos,'0123456789*',true,-1);
    wstr = wstrPos[0];
    pos = wstrPos[1]; 
    if (wstr === null) { return null; }
    if (wstr !== '') { fmt.width = (wstr==='*') ? '*' : Number(wstr); }

    // precision
    if (pos >= format.length) { return null; }
    ch = format[pos];
    if (ch === '.') { 
        pstrPos = $pj.next_token(format,pos+1,'0123456789*',true,-1);
	pstr=pstrPos[0];
	pos=pstrPos[1];
        if (pstr === null) { return null; }
        if (pstr !== '') { fmt.precision = (pstr==='*') ? '*' : Number(pstr); }
        if (pos >= format.length) { return null; }
        ch = format[pos];        
    }

    // length modifier (ignore this)
    lstrPos = $pj.next_token(format,pos,"lh",true,-1);
    lstr=lstrPos[0];
    pos=lstrPos[1];
    if (lstr === null) { return null; }
    if (pos >= format.length) { return null; }
    ch = format[pos];    

    // code
    if ("srcdiuoxXeEfFgG".indexOf(ch) === -1) { return null; }
    fmt.code = ch; 
    fmt.pos = pos;
    return fmt;
}

$pj.apply_format = function(fmt,values,counter) {
    var width = -1;
    var precision = 6;

    if (fmt.width !== null) {
        width = fmt.width;
        if (width === '*') { width = Number(values[counter++]); }
    }

    if (fmt.precision !== null) {
        precision = fmt.precision;
         if (precision === '*') { precision = Number(values[counter++]); }
    }

    if (fmt.key !== null) {
        val = values[fmt.key];
    } else {
        val = values[counter++];
    } 

    var result = null;
    var absval = null;
    var numeric = true;
    switch(fmt.code) {
        case 'r':
            numeric = false;
            if (val.__repr__) {
                result = val.__repr__();
                break;            
            }
        case 's': 
        case 'c':
            numeric = false;
            result = String(val); 
            break;
        case 'i':
        case 'u': 
        case 'd':
            absval = Math.abs(val);
            result = String(Math.floor(absval));
            break;
        case 'o':
            absval = Math.abs(val);
            result = '';
            if (fmt.alternate && val !== 0) {
                result += '0';
            }
            result += absval.toString(8);
            break;
        case 'x':
        case 'X':
            absval = Math.abs(val);
            result = '';
            if (fmt.alternate) {
                result += '0x';
            }
            result += absval.toString(16);
            break;
        case 'f':
        case 'F':
        case 'g':
        case 'G':
            absval = Math.abs(val);
            var decimal_range = ((absval === 0) || (absval >= 0.0001 && absval < 1000000));
            if (!((fmt.code === 'g') || (fmt.code === 'G')) || decimal_range) { 
                if (fmt.code === 'g' || fmt.code === 'G') {
                    var integerval = Math.floor(absval);
                    var integerstr = integerval.toString();
                    // if (integerstr !== "0") {
                        if (fmt.code === 'g' || fmt.code === 'G') {
                            precision = precision - integerstr.length;
                        }
                    // }
                    if (precision < 0 || ((absval - integerval) === 0) && !fmt.alternate) {
                        precision = 0;
                    }
                }
                result = absval.toFixed(precision);
                break;
            }
        case 'e':
        case 'E':
            absval = Math.abs(val);
            if (fmt.code === 'g' || fmt.code === 'G') {
                if (precision > 1) {
                    precision--;
                }
            }
            result = absval.toExponential(precision);
            var plus = result.indexOf('e')
            if (plus !== -1) {
                var s = result.slice(plus+2);
                if (s.length === 1) {
                    result = result.slice(0,plus+2)+"0"+s;
                }
            }
            break;            
        default: 
            result = "?";
    }
    
    var signchar = null;
    if (numeric) {
        if (val < 0) {
            signchar = '-';
        } else if (fmt.useplus) { 
            signchar = '+';
        } else if (fmt.space_pad) { 
            signchar = " "; 
        }
    }

    if (fmt.code === 'X' || fmt.code === 'E' || fmt.code === 'G' || fmt.code === 'F') {
        result = result.toUpperCase();
    }

    var pad = ' ';
    if (fmt.zero_pad) {
        pad = '0';
    }

    if ((fmt.ljust || !fmt.zero_pad) && signchar) {
        result = signchar + result;
        signchar = null;    
    }

    if (width !== -1) {
        w = result.length;
        if (signchar) {
            w = w + 1;
        }
        while(w < width) {
            if (fmt.ljust) {
                result = result + ' ';
            } else {
                result = pad + result;
            }
            w++;
        }
    }

    if (signchar) {
        result = signchar + result;
    }

    return [result,counter];
}    

$pj.mod_format = function(a1,a2) {
    if (a1 instanceof Number || typeof(a1) === 'number') {
        return (a1 % a2);
    }    
    var mapping_format = false;
    //var tystr = typeof(a2);
    if ((!(a2 instanceof Array)) && (!(typeof(container) === 'array'))) { // (tystr === 'string' || tystr === 'number' || a2 isinstance of Number ) {
        a2 = [a2];       
    } 
    var result = '';
    var index = 0;
    var i = 0;
    var conv_counter = 0;
    while(i<a1.length) {
        if (a1[i] === '%') {
            if (i+1 === a1.length) {
                result += '%';
                i += 1;
            } 
            else if (a1[i+1] === '%') {
                result += '%';
                i += 2;
            }
            else {
                var fmt = $pj.parse_format(a1,i);
                i = fmt.pos;
                sConv_counter = $pj.apply_format(fmt,a2,conv_counter);               
		s=sConv_counter[0];
		conv_counter=sConv_counter[1];
                result += s;
            }
        } else {
            result += a1[i];
        }
        i++;
    }
    return result;
}

$pj.filter = function(fn,list) {
    var results = [];
    var i = 0;
    for(i=0; i<list.length; i++) {
        v = list[i];
        if (fn(v)) {
            results.push(v);
        }
    }
    return results;
}

$pj.reduce = function(fn,list) {
    var pos = 0;
    var result = null;
    if (arguments.length === 3) {
        result = arguments[2];
    }
    if (result === null) {
        pos = 1;
        result = list[0];    
    }

    for(i=pos;i<list.length;i++) {
        result = fn(result,list[i]);
    }    

    return result;
}

$pj.zip = function() {
    
    if (arguments.length === 0) {
        return [];
    }

    var results = [];
    var pos = -1;
    var i = 0;
    var cont = true;
    while(cont) {
        pos++;
        for(i=0;i<arguments.length;i++) {
            if (pos >= arguments[i].length) {
                cont = false;
                break;
            }
        }
        if (cont) {
            var newitem = [];
            for(i=0; i<arguments.length;i++) {
               newitem.push(arguments[i][pos]);
            }
            results.push(newitem);
        }
    }
    return results;
}

$pj.count = function(str,sub,start,end) {
    if (str.count) { return str.count(sub,start,end);}
    var pos = 0;
    if (start !== undefined) {
        if (start < 0) {
            start = str.length + start;
        }
        if (start < 0) {
            start = 0;
        }
        pos = start;
    }    
    if (end !== undefined) {
        if (end < 0) {
            end = str.length + end;
        } 
        if (end < 0) {
            end = 0;
        }
    }
    pos = str.indexOf(sub,pos);
    var count = 0;
    while(pos >= 0) {
        if (end !== undefined) {
            if (pos+sub.length > end) {
                break;
            }
        }
        count++;
        pos += sub.length;
        pos = str.indexOf(sub,pos);
    }
    return count;
}


$pj.choice = function(s) {
    return (s[$pj.int((Math.random()*$pj.len(s)))]);
}


$pj.randint = function(s1, s2) {
    return $pj.int((Math.random()*(s2-s1))+s1);
}

$pj.randrange1 = function(s1) {
    return $pj.int((Math.random()*s1));
}

$pj.randrange2 = function(s1, s2) {
    return $pj.int((Math.random()*(s2-s1))+s1);
}

$pj.randrange3 = function(s1, s2, s3) {
    return $pj.int((s3>0)? (Math.random()*(s2-s1)*s3)+s1 : (Math.random()*(s1-s2)*-s3)+s2);
}

$pj.match = function(s1, s2) {
    return RegExp(s1[0]!=='^'?'^'+s1:s1,'gm').exec(s2);
}

$pj.cmp = function(s1, s2) {
    return (s1 > s2 ? 1 : s1 < s2 ? -1 : 0);
}

$pj.append = function(s0,s1) {
    return (s0.append ? s0.append(s1) : s0.push(s1))
}

$pj.upper = function(s0) {
    return (s0.upper ? s0.upper(s1) : s0.toUpperCase());
}

$pj.lower = function(s0) {
    return (s0.lower ? s0.lower(s1) : s0.toLowerCase());
}


$pj.find = function(s0,s1) {
    return (s0.find ? s0.find(s1) : s0.indexOf(s1));
}

$pj.index = function(s0,s1) {
    return (s0.index ? s0.index(s1) : s0.indexOf(s1));
}

$pj.rfind = function(s0,s1) {
    return (s0.rfind ? s0.rfind(s1) : s0.lastIndexOf(s1));
}



$pj.atoi = function(s) {
    if (isNaN(s)) {
        // warning text nicked from python ValueError
        throw(new  $pj.ValueError("invalid literal for int: "+String(s)));
    }
    return new Number(s);
}


$pj.str = function(v) {
    if (v && v.toFixed) {
        if (Math.floor(v) !== v) {
            return v.toFixed(12);
        }
    }
    if (!(s instanceof String) && !(typeof(s) !== 'string')) {
        return new String(v);
    }
    return v;
}

$pj.isinstance = function(s1,s2) {
    return ((s1 === null || s1 === undefined) ? false: (s1 instanceof s2 || (s1.$classess && s1.$classess.indexOf(s2)!==-1)));
}

$pj.get1 = function(s0,s1) {
    return ((s0 && typeof(s0.get) === 'function')  ? s0.get(s1) : s0[s1]);
}

$pj.get2 = function(s0,s1,s2) {
    return ((s0 && typeof(s0.get) === 'function') ? s0.get(s1,s2) : ((s1 in s0) ? s0[s1] : s2));
}

$pj.set = function(s0,s1,s2) {
    return (s0.set ? s0.set(s1,s2) : s0[s1] = s2);
}


// this will not return the same number as a python hash. do not
// depend on the hash code between implementations.
$pj.hash = function(s) {
    if (s.__hash__) { return s.__hash__(); }
    if (s.__pj_hashCode__ !== undefined) { return s.__pj_hashCode__;}
    if (!(s instanceof String) && !(typeof(s) !== 'string')) {
	s2 = $pj.str(s);
    }
    var h = 0;
    var len = s2.length;
    var i;
    var c;
    if (len === 0) { return 0; }
    for (i=0; i<len;i++) {
	c=s2.charCodeAt(i);
	h=((h<<5)-h) + c;
	h = h & h // convert to 32 bit
    }
    s.__pj_hashCode__ = h
    return h
}

//BEGIN JSON-SANS-EVAL
//JSON-SANS-EVAL - This source code is free for use in the public domain.
// NO WARRANTY EXPRESSED OR IMPLIED. USE AT YOUR OWN RISK.

// http://code.google.com/p/json-sans-eval/
/*
 * @param {string} json per RFC 4627
 * @param {function (this:Object, string, *):*} opt_reviver optional function
 *     that reworks JSON objects post-parse per Chapter 15.12 of EcmaScript3.1.
 *     If supplied, the function is called with a string key, and a value.
 *     The value is the property of 'this'.  The reviver should return
 *     the value to use in its place.  So if dates were serialized as
 *     {@code { "type": "Date", "time": 1234 }}, then a reviver might look like
 *     {@code
 *     function (key, value) {
 *       if (value && typeof value === 'object' && 'Date' === value.type) {
 *         return new Date(value.time);
 *       } else {
 *         return value;
 *       }
 *     }}.
 *     If the reviver returns {@code undefined} then the property named by key
 *     will be deleted from its container.
 *     {@code this} is bound to the object containing the specified property.
 * @return {Object|Array}
 * @author Mike Samuel <mikesamuel@gmail.com>
 */

$pj.readJson = (function () {
  var number
      = '(?:-?\\\\b(?:0|[1-9][0-9]*)(?:\\\\.[0-9]+)?(?:[eE][+-]?[0-9]+)?\\\\b)';
  var oneChar = '(?:[^\\\\0-\\\\x08\\\\x0a-\\\\x1f\\"\\\\\\\\]'
      + '|\\\\\\\\(?:[\"/\\\\\\\\bfnrt]|u[0-9A-Fa-f]{4}))';
  var string = '(?:\\"' + oneChar + '*\\")';

  // Will match a value in a well-formed JSON file.
  // If the input is not well-formed, may match strangely, but not in an unsafe
  // way.
  // Since this only matches value tokens, it does not match whitespace, colons,
  // or commas.
  var jsonToken = new RegExp(
      '(?:false|true|null|[\\\\{\\\\}\\\\[\\\\]]'
      + '|' + number
      + '|' + string
      + ')', 'g');

  // Matches escape sequences in a string literal
  var escapeSequence = new RegExp('\\\\\\\\(?:([^u])|u(.{4}))', 'g');

  // Decodes escape sequences in object literals
  var escapes = {
    '"': '"',
    '/': '/',
    '\\\\': '\\\\',
    'b': '\\b',
    'f': '\\f',
    'n': '\\n',
    'r': '\\r',
    't': '\\t'
  };
  function unescapeOne(_, ch, hex) {
    return ch ? escapes[ch] : String.fromCharCode(parseInt(hex, 16));
  }

  // A non-falsy value that coerces to the empty string when used as a key.
  var EMPTY_STRING = new String('');
  var SLASH = '\\\\';

  // Constructor to use based on an open token.
  var firstTokenCtors = { '{': Object, '[': Array };

  var hop = Object.hasOwnProperty;

  return function (json, opt_reviver) {
    // Split into tokens
    var toks = json.match(jsonToken);
    // Construct the object to return
    var result;
    var tok = toks[0];
    var topLevelPrimitive = false;
    if ('{' === tok) {
      result = {};
    } else if ('[' === tok) {
      result = [];
    } else {
      // The RFC only allows arrays or objects at the top level, but the JSON.parse
      // defined by the EcmaScript 5 draft does allow strings, booleans, numbers, and null
      // at the top level.
      result = [];
      topLevelPrimitive = true;
    }

    // If undefined, the key in an object key/value record to use for the next
    // value parsed.
    var key;
    // Loop over remaining tokens maintaining a stack of uncompleted objects and
    // arrays.
    var stack = [result];
    for (var i = 1 - topLevelPrimitive, n = toks.length; i < n; ++i) {
      tok = toks[i];

      var cont;
      switch (tok.charCodeAt(0)) {
        default:  // sign or digit
          cont = stack[0];
          cont[key || cont.length] = +(tok);
          key = void 0;
          break;
        case 0x22:  // '"'
          tok = tok.substring(1, tok.length - 1);
          if (tok.indexOf(SLASH) !== -1) {
            tok = tok.replace(escapeSequence, unescapeOne);
          }
          cont = stack[0];
          if (!key) {
            if (cont instanceof Array) {
              key = cont.length;
            } else {
              key = tok || EMPTY_STRING;  // Use as key for next value seen.
              break;
            }
          }
          cont[key] = tok;
          key = void 0;
          break;
        case 0x5b:  // '['
          cont = stack[0];
          stack.unshift(cont[key || cont.length] = []);
          key = void 0;
          break;
        case 0x5d:  // ']'
          stack.shift();
          break;
        case 0x66:  // 'f'
          cont = stack[0];
          cont[key || cont.length] = false;
          key = void 0;
          break;
        case 0x6e:  // 'n'
          cont = stack[0];
          cont[key || cont.length] = null;
          key = void 0;
          break;
        case 0x74:  // 't'
          cont = stack[0];
          cont[key || cont.length] = true;
          key = void 0;
          break;
        case 0x7b:  // '{'
          cont = stack[0];
          stack.unshift(cont[key || cont.length] = {});
          key = void 0;
          break;
        case 0x7d:  // '}'
          stack.shift();
          break;
      }
    }
    // Fail if we've got an uncompleted object.
    if (topLevelPrimitive) {
      if (stack.length !== 1) { throw new Error(); }
      result = result[0];
    } else {
      if (stack.length) { throw new Error(); }
    }

    if (opt_reviver) {
      // Based on walk as implemented in http://www.json.org/json2.js
      var walk = function (holder, key) {
        var value = holder[key];
        if (value && typeof value === 'object') {
          var toDelete = null;
          for (var k in value) {
            if (hop.call(value, k) && value !== holder) {
              // Recurse to properties first.  This has the effect of causing
              // the reviver to be called on the object graph depth-first.

              // Since 'this' is bound to the holder of the property, the
              // reviver can access sibling properties of k including ones
              // that have not yet been revived.

              // The value returned by the reviver is used in place of the
              // current value of property k.
              // If it returns undefined then the property is deleted.
              var v = walk(value, k);
              if (v !== void 0) {
                value[k] = v;
              } else {
                // Deleting properties inside the loop has vaguely defined
                // semantics in ES3 and ES3.1.
                if (!toDelete) { toDelete = []; }
                toDelete.push(k);
              }
            }
          }
          if (toDelete) {
            for (var i = toDelete.length; --i >= 0;) {
              delete value[toDelete[i]];
            }
          }
        }
        return opt_reviver.call(holder, key, value);
      };
      result = walk({ '': result }, '');
    }

    return result;
  };
})();

//END JSON-SANS-EVAL

$pj.Generator = function (container) {
        var isarray = ((typeof(container) === 'array') || (container instanceof Array));
        var isstring = ((typeof(container) === 'string') || (container instanceof String));
        this.iterator=null;
        if (isarray || isstring) {
                this.values = container;
        } else if (container.__iter__) {
                this.values = [];
                this.iterator = container.__iter__();
        } else {
                this.values = [];
                for(key in container) {
                        this.values.push(key);
                }
        }
        this.index = 0;
        this.iterator_exhausted=false;
}

$pj.Generator.prototype.nextValue = function() {
        if (this.iterator) {
                try {
                        return this.iterator.next();
                } catch( e ) {
                        this.iterator_exhausted = true;
                        return null;
                }
        }
        else if (this.index < this.values.length) {
                return this.values[this.index++];
        } else {
                this.index++;
                return null;
        }
}

$pj.Generator.prototype.hadMore = function() {
        if (this.iterator_exhausted) {
                return false;
        }
        return (this.index-1) < this.values.length;
}

$pj.ValueError = function (details) {
    this.details = details;
    return this;
}


"""


mappedFuncs = { 
    'math.abs' : 'Math.abs',
    'math.acos' : 'Math.acos',
    'math.asin' : 'Math.asin',
    'math.atan' : 'Math.atan',
    'math.atan2' : 'Math.atan2',
    'math.ceil' : 'Math.ceil',
    'math.cos' : 'Math.cos',
    'math.exp' : 'Math.exp',
    'math.floor' : 'Math.floor',
    'math.log' : 'Math.log',
    'math.pow' : 'Math.pow',
    'math.random' : 'Math.random',
    'math.round' : 'Math.round',
    'math.sin' : 'Math.sin',
    'math.sqrt' : 'Math.sqrt',
    'math.sqrt' : 'Math.sqrt',
    'math.tan' : 'Math.tan',
    'random.random': 'Math.random',
    'random.randint': '$pj.randint(%1, %2)',
    'random.choice': '$pj.choice',
    'random.randrange.1': '$pj.randrange1(%1)',
    'random.randrange.2': '$pj.randrange2(%1, %2)',
    'random.randrange.3': '$pj.randrange2(%1, %2, %3)',
    'type': 'typeof',
    'hasattr' : '(%1[%2] !== undefined)',
    'getattr' : '(%1[%2])',
    'datetime.datetime' : '(new Date(%*))',
    're.sub.2' : '%3.replace(RegExp(%1,"gm"), %2)', # FIXME. todo, overload the RegExp prototype to add sub, search, and match
    're.compile' : 'RegExp(%1,"gm")', 
    're.search' : 'RegExp(%1,"gm").exec(%2)',
    're.match' : "$pj.match(%1, %2)",
    #'re.search.3' : None, # todo, check for ignorecase
    #'re.match.3' : None,
    'cmp' : '$pj.cmp(%1, %2)',
    'len' : '$pj.len(%1)',
    '.append' : '$pj.append(%0, %1)',
    'sum' : '$pj.sum',
    'list': '$pj.map(null, %1)',
    'tuple': '$pj.map(null, %1)',
    'map.2' : '$pj.map(%1,%2)',
    #'map.3' : None,
    #'map.4' : None,
    #'map.5' : None,
    #'map.6' : None,
    'reduce' : '$pj.reduce',
    'zip' : '$pj.zip',
    'filter' : '$pj.filter',
    'min.1' : '$pj.min(%1)',
    'min.2' : '$pj.min([%1,%2])',
    'max.1' : '$pj.max(%1)',
    'max.2' : '$pj.max([%1,%2])',
    '.remove' : '$pj.remove(%0,%1)',
    '.sort.0' : 'sort',
    '.sort.1' : 'sort',
    '.sort.2' : '$pj.sort3(%0,%1,%2,false)',
    '.sort.3' : '$pj.sort3(%0,%1,%2,%3)',
    'xrange.1' : '$pj.xrange2(0,%1)',
    'xrange.2' : '$pj.xrange2(%1,%2)',
    'xrange.3' : '$pj.xrange2(%1,%2,%3)',
    'range.1' : '$pj.xrange2(0,%1)',
    'range.2' : '$pj.xrange2(%1,%2)',
    'range.3' : '$pj.xrange2(%1,%2,%3)',
    '.extend' : '%0.concat(%1)', 
    'extendRet' : '%1.concat(%*)', 
# conversion
    'str' : '$pj.str(%1)',
    'int' : '(%1 | 0)',
    'float' : '(%1)',
    'ord' : '%1.charCodeAt(0)',
    'chr' : 'String.fromCharCode(%1)',
    'hash' : '$pj.hash(%1)',
# strings
    '.upper' : '$pj.upper(%0)',
    '.lower' : '$pj.lower(%0)',
    '.find' : '$pj.find(%0,%1)',
    '.index' : '$pj.index(%0,%1)',
    '.rfind' : '$pj.rfind(%0,%1)',
    '.splitlines.1' : '%0.split(%1)', #fixme
    '.splitlines.0' : '%0.split("\\n")',
    '.split.2'  : '%0.split(%1,%2)',
    '.split.1' : '%0.split(%1)',
    '.split.0' : '%0.split(/\s+/)',
    '.join.1' : '%1.join(%0)',
    '.replace' : '$pj.replace(%0,%1,%2)',
    '.count' : '$pj.count(%0,%*)',
    '.rstrip.0' : '$pj.rstrip(%0,"\\n\\t ")',
    '.rstrip.1' : '$pj.rstrip(%0,%1)',
    '.lstrip.0' : '$pj.lstrip(%0,"\\n\\t ")',
    '.lstrip.1' : '$pj.lstrip(%0,%1)',
    '.strip.0' : '$pj.strip(%0,"\\n\\t ")',
    '.strip.1' : '$pj.strip(%0,%1)',
    'string.atoi' : '$pj.atoi(%1)',
    'string.upper' : '%1.toUpperCase()',
    'string.lower' : '%1.toLowerCase()',
    'string.find' : '%1.indexOf(%2)',
    'string.index' : '%1.indexOf(%2)',
    'string.rfind' : '%1.lastIndexOf(%2)',
    'string.splitlines.2' : '%1.split(%2)',
    'string.splitlines.1' : '%1.split("\\n")',
    'string.split.3'  : '%1.split(%2).slice(%3 - 1)',
    'string.split.2' : '%1.split(%2)',
    'string.split.1' : '%1.split(/\s+/)',
    'string.replace.3' : '$pj.replace(%1,%2,%3)',
    'string.count' : '$pj.count(%1,%*)',
    'string.rstrip.1' : '$pj.rstrip(%1,"\\n\\t ")',
    'string.rstrip.2' : '$pj.rstrip(%1,%2)',
    'string.lstrip.1' : '$pj.lstrip(%1,"\\n\\t ")',
    'string.lstrip.2' : '$pj.lstrip(%1,%2)',
    'string.strip.1' : '$pj.strip(%1,"\\n\\t ")',
    'string.strip.2' : '$pj.strip(%1,%2)',

#general
    'copy.copy' : '$pj.copy(%1)', 
    'copy.deepcopy' : '$pj.deepcopy(%1)',
    'isinstance' : '$pj.isinstance(%1, %2)',
    '.get.1' : '$pj.get1(%0,%1)',
    '.get.2' : '$pj.get2(%0,%1,%2)',
    '.set.2' : '$pj.set(%0,%1,%2)',
    '.clear.0' : '(%0.clear ? %0.clear() : %0 = {})', # this may be a problem because of the multi use of %0, if %0 is an expression.
    '.iteritems.0' : '$pj.items(%0)',
    '.items.0' : '$pj.items(%0)',
    '.values.0' : '$pj.values(%0)',
    '.keys' : '$pj.keys(%0)',
    '.has_key' : '$pj.has_key(%0,%1)',
    #'super' : '%1.super(%2)' # TODO
}


mdict = {}
class_aliases = {}

class BackendException(Exception):

    def __init__(self,detail):
        self.detail = detail

class BackendNotImplementedException(BackendException):

    def __init__(self,detail):
        BackendException.__init__(self,detail)

    def __str__(self):
        return "Cannot generate javascript for: " + self.detail

class BackendInternalErrorException(BackendException):

    def __init__(self,detail):
        BackendException.__init__(self,detail)

    def __str__(self):
        return "JavaScript Backend Generator: " + self.detail

loaded_paths = []
class GenVisitor(ScopeManager):
    loaded_modules = []
    def __init__(self,module_name,module_path,module_namespace):
        self.loaded_modules.append(module_namespace)
        self.uops = { 'Not':'not', 'UAdd':'+', 'USub':'-', 'Invert':'~' }
        self.bops = { 'Is':"==",  'IsNot':"!=", 'Eq':"==", 'NotEq':'!=', 'Mult':"*", 'Sub':"-", 'Lt':'<', 'LtE':'<=', 'Gt':'>', 'GtE':'>=', 'Add':'+', 'Mod':'%', 'And':'and', 'Or':'or', 'Div':'/', 'Pow':'**', 'In':'in', 'NotIn':'not in', 'RShift':'>>', 'LShift':'<<', 'BitOr':'|', 'BitXor':'^', 'BitAnd':'&', 'FloorDiv':'//' }
        self.aops = { 'Add':'+=', 'Sub':'-=', 'Mult':'*=', 'Div':'/=', 'Mod':'%=', 'Pow':'**=', 'RShift':'>>=', 'LShift':'<<=', 'BitOr':'|=', 'BitXor':'^=', 'BitAnd':'&=', 'FloorDiv':'//=' }
        self.module = None
        self.module_name = module_name
        self.module_path = module_path
        self.module_namespace = module_namespace
        self.skip = False
        self.module_depends = []
        ScopeManager.__init__(self)

    def parse(self,contents):
        regex = re.compile("\r\n")
        contents = regex.sub(r'\n', contents)    
        ast = compile(str(contents), '<string>', 'exec', _ast.PyCF_ONLY_AST)
        return self.visit(ast)

    def visit(self,ast):
        if ast == None:
            return None
        name = ast.__class__.__name__
        if self.skip and name not in ('Expr', 'Str'):
            return []
        if hasattr(self,name):
            val = getattr(self,name)(ast)
            return val
        else:
            raise FrontendException("No handler for AST object: "+name,ast.lineno, self.module.path)

   
# expressions

    def Attribute(self,ast):
        obj = self.visit(ast.value)
        attr = ast.attr
        return AttributeLookup(obj,attr)

    def BinOp(self,ast):
        op = self.bops[ast.op.__class__.__name__]
        lhs = self.visit(ast.left)
        rhs = self.visit(ast.right)
        return BinaryOp(op,lhs,rhs)

    def BoolOp(self,ast):
        op = self.bops[ast.op.__class__.__name__]
        values = ast.values
        assert(len(values)>1)
        for idx in xrange(0,len(values)):
            values[idx] = self.visit(values[idx])
        expr = None
        start = len(values)-2
        while start >= 0:
            if expr == None:
                expr = BinaryOp(op,(isinstance(values[start],BinaryOp) or isinstance(values[start],UniOp)) and values[start] or FunctionCall("$pj.t", [values[start]], {}),(isinstance(values[start+1],BinaryOp) or isinstance(values[start+1],UniOp)) and values[start+1] or FunctionCall("$pj.t", [values[start+1]], {}))
            else:
                expr = BinaryOp(op,(isinstance(values[start],BinaryOp) or isinstance(values[start],UniOp)) and values[start] or FunctionCall("$pj.t", [values[start]], {}),expr)
            start -= 1
        return expr

    def Call(self,ast):
        args = []
        kwargs = {}
        for keyword in ast.keywords:
            key = VarName(keyword.arg)
            kwargs[key] = self.visit(keyword.value)
        for a in xrange(0,len(ast.args)):
            arg = self.visit(ast.args[a])
            args.append(arg)
        if ast.func.__class__.__name__ == 'Attribute':
            target = self.visit(ast.func.value)
            return MethodCall(target,ast.func.attr,args,kwargs)
        if ast.func.__class__.__name__ == 'Subscript':
            target = self.visit(ast.func)
            return FunctionCall(target,args,kwargs)
        fname = ast.func.id 
        if fname == "JS":
            return Verbatim(args[0].value,exp=True)
        if fname == "JSMap":
            dictv = args[0]
            nr = len(dictv.keyvalues)
            for idx in xrange(0,nr):
                (key,value) = dictv.keyvalues[idx]
                mappedFuncs[key.value] = value.value
            return Verbatim("")
        return FunctionCall(fname,args,kwargs)

    def Compare(self,ast):
        result = None
        lhs = self.visit(ast.left)
        for index in xrange(0,len(ast.ops)):
            op = self.bops[ast.ops[index].__class__.__name__]
            rhs = self.visit(ast.comparators[index])
            clause = BinaryOp(str(op),lhs,rhs)
            if result == None:
                result = clause
            else:
                result = BinaryOp("and",result,clause)
            lhs = rhs    
        return result
        
    def comprehension(self, ast):
        t = self.visit(ast.target)
        i = self.visit(ast.iter)
        cond = None   
        for e in ast.ifs:
            target = self.visit(e.left)   
            for index in xrange(0,len(e.ops)):
                c = self.visit(e.comparators[index])
                op = e.ops[index].__class__.__name__
                if op in self.bops:
                    op = self.bops[op]
                else:
                    raise FrontendException('Binary Operaton:'+op,ast.lineno, self.module.path)                               
                bop = BinaryOp(op,target,c)
                if cond:
                    cond = BinaryOp('and',cond,bop)
                else:
                    cond = bop    
        return ListComprehensionGenerator(t,i,cond)

    def Dict(self, ast):       
        keyvals = []
        for idx in xrange(0,len(ast.keys)):
            key = ast.keys[idx]
            value = ast.values[idx]
            keyvals.append((self.visit(key),self.visit(value)))
        return DictionaryValue(keyvals)

    def Expr(self, ast):
        expr = self.visit(ast.value)
        if not expr: return []
        return [ExpressionStatement(expr)]

    def GeneratorExp(self, ast):
        # it seems that generator expressions can be handled
        # in the same way as list comprehensions!
        return self.ListComp(ast)

    def Index(self,ast):
        return self.visit(ast.value)

    def Lambda(self, ast):
        args = []
        l = Lambda(None,None)
        self.pushScope(l)
        for a in ast.args.args:
            if a.__class__.__name__ == 'Tuple':
                print  "warning: tuple in lambda arg", self.module_name, ast.lineno
                for e in a.elts:
                    args.append(e.id)
                    self.addGlobal(e.id)
            else:
                args.append(a.id)
                self.addGlobal(a.id)
        l.args = args
        body = self.visit(ast.body)
        self.popScope()
        l.body = body
        return l

    def List(self,ast):
        elements = []
        for e in ast.elts:
            elements.append(self.visit(e))
        return ListValue(elements)

    def ListComp(self, ast):
        e = self.visit(ast.elt)
        generators = []
        for g in ast.generators:
                generators.append(self.visit(g))
        return ListComprehension(e,generators)

    def Name(self,ast):
        if ast.id == 'True':
            return Literal(True)
        elif ast.id == 'False':
            return Literal(False)
        elif ast.id == 'None':
            return Literal(None)
        return VarName(ast.id)  

    def Num(self,ast):
        return Literal(ast.n)

    def Slice(self,ast):
        return (self.visit(ast.lower),self.visit(ast.upper),self.visit(ast.step))

    def Str(self,ast):
        return Literal(ast.s)

    def Subscript(self,ast):
        op = "[]"
        arg = self.visit(ast.value)
        index = self.visit(ast.slice)
        if isinstance(index,tuple):
            # slice operation
            return SliceOp(arg,index)
        else:
            return BinaryOp(op,arg,index)

    def Tuple(self,ast):
        return self.List(ast)
      
    def UnaryOp(self,ast):
        op = self.uops[ast.op.__class__.__name__]
        if op == "not" and not (isinstance(ast.operand,BinaryOp) or isinstance(ast.operand,UniOp)):
            arg = FunctionCall("$pj.t", [self.visit(ast.operand)], {})
        else:
            arg = self.visit(ast.operand)
        return UniOp(op,arg)

# Blocks and statements

    def makeBlock(self,code):
        if not (isinstance(code,Block)):
            return Block([code])
        else:
            return code

    def Assign(self, ast):
        target = self.visit(ast.targets[0])
        expr = self.visit(ast.value)
        adef = AssignmentStatement(target, expr)
        ret = []
        ret.append(adef)
        if len(ast.targets) != 1:
            for target2 in ast.targets[1:]:
                adef = AssignmentStatement(self.visit(target2), target)
                ret.append(adef)
        if isinstance(self.getInnerScope(), Module) or isinstance(self.getInnerScope(), ClassDefinitionStatement):
            for adef in ret:
                walker = VarNameWalker()
                adef.target.walk(walker)
                varnames = walker.getVarNames()
                for varname in varnames:
                    self.addGlobal(varname)
        return ret

    def AugAssign(self, ast):
        target = self.visit(ast.target)
        op = self.aops[ast.op.__class__.__name__]
        expr = self.visit(ast.value)
        adef = AugmentedAssignmentStatement(target, op, expr)
        return [adef]

    def Break(self,ast):
        bdef = BreakStatement()
        return [bdef]

    def ClassDef(self,ast):
        name = ast.name
        subclasses = []
        bases = []
        for base in ast.bases:
            bases.append(base.id)
        memberfns = []
        staticvars = []
        constructor = None
        self.addGlobal(name)
        cdef = ClassDefinitionStatement(name,self.module)
        self.pushScope(cdef)

        # add some JS/Python specific globals
        self.addGlobal("$self")
        self.addGlobal("$classess")
        #self.addGlobal("super")

        for stmt in ast.body:
            stmts = self.visit(stmt)
            for b in stmts:
                if isinstance(b,FunctionDefinitionStatement):
                    if b.fname == '__init__':
                        constructor = b
                    else:
                        memberfns.append(b)
                elif isinstance(b,ClassDefinitionStatement):
                    b.setParentClass(cdef)
                    subclasses.append(b)                
                elif isinstance(b,AssignmentStatement):
                    staticvars.append((b.target,b.expr))
                elif isinstance(b,EmptyStatement):
                    pass
                elif isinstance(b,ExpressionStatement):
                    pass # perhaps a docstring?  FIXME - need to check
                else:
                    raise FrontendException("class contents except for member variables, classes and functions",ast.lineno, self.module.path)
        cdef.configure(bases,constructor,memberfns,staticvars,subclasses)       
        self.module.addClassMountPoint(name,cdef.getClassNamespace())        
        self.popScope()
        return [cdef]+subclasses

    def Continue(self,ast):
        cdef = ContinueStatement()
        return [cdef]

    def Delete(self, d):
        dels = []
        for target in d.targets:
            dels.append(DeleteStatement(self.visit(target)))
        return dels

    # python 2.6
    def ExceptHandler(self, ast):
        return self.excepthandler(ast) 

    def excepthandler(self, ast):
        etype = None
        if ast.type:
            etype = ast.type.id
        ename = None
        if ast.name:
            ename = ast.name.id
        body = self.Statements(ast.body)
        edef = ExceptionHandlerStatement(etype,ename,body)
        return edef

    def For(self, ast):        
        target = self.visit(ast.target)
        if not isinstance(target,VarName):
            raise FrontendException("complex target in for loop not supported",ast.lineno, self.module.path)
        loopexpr = self.visit(ast.iter)
        if isinstance(loopexpr,FunctionCall):
            if loopexpr.fname == "xrange" or loopexpr.fname == 'range':
                lwb = loopexpr.args[0]
                upb = lwb
                if len(loopexpr.args)>=2:
                    lwb = upb
                    upb = loopexpr.args[1]
                if len(loopexpr.args)==3:
                    step = loopexpr.args[2]
                else:
                    step = Literal(1)
                fdef = ForStatement(target,lwb,upb,step,None)
                self.pushScope(fdef)
                body = self.Statements(ast.body)
                fdef.block = body
                self.popScope()
                return [fdef]            
        
        fdef = ForInStatement(target,loopexpr,None)
        self.pushScope(fdef)
        body = self.Statements(ast.body)
        fdef.block = body
        self.popScope()
        return [fdef]

    def FunctionDef(self, ast):
        decorators = set()
        if 'decorator_list' in ast.__dict__:
            # python 2.6
            for decorator in ast.decorator_list:
                decorators.add(decorator.id)
        else:
            for decorator in ast.decorators:
                decorators.add(decorator.id) 
        fname = ast.name
        self.addGlobal(fname)
        fdef = FunctionDefinitionStatement(fname)
        self.pushScope(fdef)
        argnames = []
        argdefaults = []

        for d in ast.args.defaults:
            argdefaults.append(self.visit(d))
                              
        for a in ast.args.args:
            argnames.append(a.id)
            self.addGlobal(a.id)
        vararg = None
        kwarg = None
        if ast.args.vararg:
            vararg = ast.args.vararg
        if ast.args.kwarg:
            kwarg = ast.args.kwarg
        body = self.Statements(ast.body)
        if isinstance(self.getInnerScope(), Module) or isinstance(self.getInnerScope(), ClassDefinitionStatement):
            self.addGlobal(fdef.fname)
        self.popScope()
        if not fdef.yieldScope:
            fdef.configure(decorators,argnames,argdefaults,vararg,kwarg,body)
            return [fdef]
        else:
            # turn the function into a yield obj class
            cname = fname
            memberfns = []
            subclasses = []
            bases = []
            staticvars = []
            constructor = None
            cdef = ClassDefinitionStatement(cname,self.module)
            self.pushScope(cdef)
            cdef.yieldScope = True
            if True:
                fdef.fname = 'next'
                fdef.configure([],['_yieldobj'],[],None,None,body)
                memberfns.append(fdef)
            if False:
                iterFn = FunctionDefinitionStatement('__iter__')            
                ibody = Block([ReturnStatement(VarName('_yieldobj'))])
                iterFn.configure([],['_yieldobj'],[],None,None,ibody)
                memberfns.append(iterFn)                
            if True:
                constructor = FunctionDefinitionStatement('__init__')
                bodys = []
                bodys.append(AssignmentStatement(VarName('_yieldobj.state'), Literal(0)))
                for arg in argnames:
                    bodys.append(AssignmentStatement(VarName('_yieldobj.'+arg), VarName(arg)))
                cbody = Block(bodys)
                constructor.configure([],['_yieldobj'] + argnames,argdefaults,vararg,kwarg,cbody)
            cdef.configure(bases,constructor,memberfns,staticvars,subclasses)
            self.module.addClassMountPoint(cname,cdef.getClassNamespace())
            self.popScope()
            return [cdef]

    def Global(self, ast):
        globs = []
        for name in ast.names:
            globs.append(GlobalStatement(name))
            self.addGlobal(name)
        return globs

    def If(self,ast):
        tests = []
        cond = self.visit(ast.test)
        cond = (isinstance(cond,BinaryOp) or isinstance(cond,UniOp)) and cond or FunctionCall("$pj.t", [cond], {})
        main = None
        if isinstance(cond,BinaryOp):
            if isinstance(cond.left,VarName) and cond.left.varname=="__name__" and cond.right.value=="__main__":
                # wrap the whole main statement in a $main function so that the local variables don't pollute the scope of the module
                self.addGlobal('$main')
                main = FunctionDefinitionStatement('$main')
                self.pushScope(main)
        block = self.Statements(ast.body)
        tests.append((cond,block))
        elseblock = None
        if ast.orelse:
            elseblock = self.Statements(ast.orelse)
        idef = IfStatement(tests,elseblock)
        if main:
            decorators = set()
            argnames = []
            argdefaults = []
            vararg = None
            kwarg = None
            body =Block([idef])
            main.configure(decorators,argnames,argdefaults,vararg,kwarg,body)
            self.popScope()
            return [main]
        return [idef]

    def Import(self,ast):
        modules = []
        for name in ast.names:
            
            (modpath,namespace) = self.locateModule(name.name,name.asname)
            code = None         
            mname = name.name
            if name.asname and name.asname !=  "":
                mname = name.asname
            self.module.addModuleMountPoint(mname,namespace)

            if namespace not in global_modules and namespace not in self.loaded_modules:
                loaded_paths.append(modpath)
                self.module_depends.append(namespace)
                self.loaded_modules.append(namespace)
                if True:
                    code = pyread(modpath,(name.name,modpath,namespace,[]))  
                if code: modules.extend(code)

        return modules

    def ImportFrom(self,ast):
        if ast.module == "__future__":
            return []

        importall = False
        if len(ast.names)==1 and ast.names[0].name=='*':
            importall = True        
        namespace = self.module_namespace

        (modpath,namespace) = self.locateModule(ast.module,'')
        if namespace in global_modules: return []
        raise FrontendException("from Y import X not supported. Use Import.",ast.lineno, self.module.path)
        if importall == False:   
            for name in ast.names:
                aliasedname = name.name
                if name.asname and name.asname != "":                
                    aliasedname = name.asname                
                
                unaliasedname = namespace + "." + name.name
                self.module.aliases.append((aliasedname,unaliasedname))
        else:
            namespace = self.module_namespace
              
        modules = []
        if namespace not in global_modules and namespace not in self.loaded_modules:
            loaded_paths.append(modpath)
            self.module_depends.append(namespace)
            self.loaded_modules.append(namespace)                   
            code = None
            if True:
                code = pyread(modpath,(ast.module,modpath,namespace))
            #except Exception, ex:
            else:
                # cannot find file, see if there is a "module equivalent"
                if importall:
                    for modname in pj_modules:
                        if ast.module.endswith(modname):
                            jspath = os.path.join("modules","javascript",pj_modules[modname]+".js")
                            jsfile = open(jspath,"r")
                            jscode = jsfile.read()
                            return [Verbatim(jscode)]
                raise ex
            if code: modules.extend(code)     
        return modules

    def locateModule(self,module,asname):
        modpath = module
        modpath = modpath.replace(".","/")
        modpath += ".py"
        (sourcedir,sourcefile) = os.path.split(self.module_path)
        modpath = os.path.join(sourcedir,modpath)
        namespace = ''
        
        # first see if the module is located relative to the calling module, but only
        # if the calling module is the initial module (or in the same directory)
        if sourcedir != initial_module_dir:
            try:
                testf = open(modpath,"r")
                ns = module
                if asname and asname !=  "":
                    ns = name.asname
                namespace = self.module_namespace
                if namespace.rfind(".") != -1:
                    namespace = namespace[:namespace.rfind(".")]
                if namespace != "":
                    namespace += "."
                namespace += ns
                return (modpath,namespace)
            except:
                pass

        # assume that the module is relative to the top level module
        # FIXME also search the current PYTHONPATH
        modpath = module
        modpath = modpath.replace(".","/")
        modpath += ".py"
        modpath = os.path.join(initial_module_dir,modpath)
        if asname and asname != "":
            namespace = asname            
        else:
            namespace = module
        return (modpath,namespace)

    def Module(self,ast):
        namespace = self.module_path.replace("/",".").replace(".py", "")
        m = Module(self.module_name,self.module_path,namespace)
        self.module = m
        self.pushScope(m)
        modulebody = self.Statements(ast.body)
        m.configure(modulebody)
        self.popScope()
        return m

    def Pass(self,ast):
        edef = EmptyStatement()
        return [edef]

    def Print(self,ast):
        pvalues = []
        for value in ast.values:
            pvalue = self.visit(value)
            pvalues.append(pvalue)
        pdef = PrintStatement(pvalues)
        return [pdef]

    def Raise(self, r):
        rtype = None
        robj = None
        if r.type:
            rtype = self.visit(r.type)
        if r.inst:
            robj = self.visit(r.inst)
        rdef = RaiseStatement(rtype,robj)
        return [rdef]        

    def Return(self,ast):
        rvalue = self.visit(ast.value)
        rdef = ReturnStatement(rvalue)
        return [rdef]

    def Statements(self,ast):
        statements = []
        block = Block(statements)
        self.skip = False
        for s in ast:
            stmts = []
            stmts = self.visit(s)
            for stmt in stmts:
                if stmt:
                    if isinstance(stmt,ExpressionStatement):
                        expr = stmt.expr
                        if isinstance(expr,Literal):
                            val = expr.value
                            if isinstance(val,str):
                                if val.startswith('pj-verbatim:'):
                                    statements.append(Verbatim(val[len('pj-verbatim:'):]))
                                    continue
                                if val.startswith('pj-skip-begin'):
                                    self.skip = True
                                    continue
                                if val.startswith('pj-skip-end'):
                                    self.skip = False
                                    continue                
                    if not self.skip:
                        statements.append(stmt)            
        block.statements = statements
        
        return block


    def TryFinally(self, ast):
        block = self.Statements(ast.body)
        handlers = []
        if isinstance(block,Block) and len(block.statements)==1:
            stmt = block.statements[0]
            if isinstance(stmt,TryStatement):
                block = stmt.body
                handlers = stmt.handlers
        finalblock = self.Statements(ast.finalbody)
        # fixme check for else
        tdef = TryStatement(block,handlers,finalblock)
        return [tdef]

    def TryExcept(self, ast):
        block = self.Statements(ast.body)
        handlers = []
        for h in ast.handlers:
            handlers.append(self.visit(h))
        # fixme check for else

        tdef = TryStatement(block,handlers,None)
        return [tdef]
 

    def While(self, ast):
        cond = self.visit(ast.test)
        cond = (isinstance(cond,BinaryOp) or isinstance(cond,UniOp)) and cond or FunctionCall("$pj.t", [cond], {})
        body = self.Statements(ast.body)
        wdef = WhileStatement(cond,body)
        return [wdef]

    def With(self,ast):
        # with expr as something: code
        #var tmp = ast.expr
        #var something tmp.__enter__()
        #try:
        #  code
        #finally:
        #tmp.__exit__(type, value, traceback)
        raise FrontendException("with clause not supported",ast.lineno, self.module.path)

    def Yield(self,ast):
        raise FrontendException("yield clause not supported",ast.lineno, self.module.path)
        self.setYieldScope()
        yvalue = self.visit(ast.value)
        ydef = YieldStatement(yvalue)
        return ydef

    def Exec(self,ast):
        raise FrontendException("Exec clause not supported",ast.lineno, self.module.path)

escaped_subst = re.compile('@{{(!?[ a-zA-Z0-9_\.]*)}}')

class JavascriptBackend(ScopeManager):
    loaded_modules = []
    def __init__(self, argfile, homepath=""):
        self.path = argfile
        self.namespace =  argfile.replace(homepath, "").strip("/").replace("/", ".").replace(".py", "")
        JavascriptBackend.loaded_modules.append(self.namespace)            
        self.homepath = homepath
        self.code = ''
        self.indent = 0
        self.indentstr = '    '
        self.jslib_support = {}
        self.varcount = 0
        self.dependencies = []
        self.module = None
        self.module_depends = []
        self.catchvars = []
        ScopeManager.__init__(self)
        self.addJslibSupport("pj")
        
    def stripNamespace(self,name):
        return name.split(".")[-1]

    def applyNamespace(self,name,**kwargs):
        #namespace = self.namespace
        namespace = ""
        if 'namespace' in kwargs:
            namespace = kwargs['namespace']
        else:
            namespace = self.getNamespace(name)
        if namespace != "__main__" and namespace != "":
            return namespace+"."+name
        return name

    def createNamespace(self,namespace):
        pass
        #txt = create_namespace(namespace)
        #self.add(txt)

    def hasNamespace(self):
        if self.namespace != "__main__":
            return True
        return False

    def setNamespace(self,namespace):
        self.namespace = namespace
        
    def pushCatchVar(self,varname):
        self.catchvars.append(varname)

    def getCatchVar(self):
        if len(self.catchvars) == 0:
            raise BackendInternalErrorException("no catch variable")
        return self.catchvars[len(self.catchvars)-1]

    def popCatchVar(self):
        self.catchvars.pop()

    # Expression handling 
    # these functions return text with the javascript representation of the expression

    def AttributeLookup(self,adef,**kwargs):
        path = self.attributeLookupPath(adef)
        if path:
            objArr = path.split(".")
            mountpoint = self.module.getMountPoint(objArr[0])
            if mountpoint:
                objArr[0] = mountpoint
                return ".".join(objArr)
        txt = self.generate(adef.obj)
        txt += '.'
        txt += adef.attr
        return txt

 
    def attributeLookupPath(self,obj):
        if isinstance(obj,VarName):
            return obj.varname
        if isinstance(obj,AttributeLookup):
            path = self.attributeLookupPath(obj.obj)
            if path:
                return path + "." + obj.attr
            return None
        return None

    def BinaryOp(self,bop,**kwargs):        
        op = bop.op
        if op in binaryOps:
            op = binaryOps[op]
        else:
            raise BackendNotImplementedException("Binary Operation("+op+")")
        dependencies = []
        if isinstance(op,tuple):
            dependencies = op[1]
            op = op[0]
        #(,['$pj.mod_format'])
        for dependency in dependencies:
            self.addJslibSupport(dependency)

        if op == "%1[%2]":
            if (isinstance(bop.right, Literal) and  (bop.right.value == -1)):
                op = "$pj.lastEl(%1)"
                self.addJslibSupport('$pj.lastEl')

        elif op == "===":
            if (isinstance(bop.right, Literal) and  (bop.right.value == None)):
                op = "=="
            if (isinstance(bop.left, Literal) and  (bop.left.value == None)):
                op = "=="
        elif op == "!==":
            if (isinstance(bop.right, Literal) and  (bop.right.value == None)):
                op = "!="
            if (isinstance(bop.left, Literal) and  (bop.left.value == None)):
                op = "!="
        elif op == "%":
            if (isinstance(bop.left, Literal) and  isinstance(bop.left.value, StringType)) or (isinstance(bop.left, FunctionCall) and bop.left.fname == "str"):
                op = '$pj.mod_format(%1,%2)'
                self.addJslibSupport('$pj.mod_format')
            else:
                print "Warning. % used. remember to cast left hand side to string if you want to use the format operator."
                
        elif op == "*":
            if isinstance(bop.left, ListValue):
                if isinstance(bop.left.elements[0], Literal) and (bop.left.elements[0].value==None):
                    return 'Array('+self.generate(bop.right)+')'
                raise BackendNotImplementedException("Binary Operation("+op+"). No auto fill in Array constructor. Value supplied is "  + str(bop.left.elements[0]))

        if op.find("%1") == -1 and op.find("%2") == -1:
            op = "%1 "+op+" %2"
        txt = ''
        if not 'toplevel' in kwargs:
            txt += "("
        lhtxt = self.generate(bop.left)        
        rhtxt = self.generate(bop.right)
        txt += self.expand(op,[lhtxt,rhtxt])
        if not 'toplevel' in kwargs:
            txt += ")"
        return txt

    def DictionaryValue(self,dictv,**kwargs):
        rollOutDict = False
        txt2 = '(function (d) {'
        txt = '{'
        nr = len(dictv.keyvalues)
        for idx in xrange(0,nr):
            (key,value) = dictv.keyvalues[idx]
            ktxt = self.generate(key)
            vtxt = self.generate(value)
            if 'ignoreFuncExpand' not in kwargs and not isinstance(key, Literal):
                rollOutDict = True
                txt2 += 'd['+ktxt+']='
                txt2 += vtxt +'; '
            else:
                if idx > 0:
                    txt += ','
                txt += ktxt + ":" + vtxt
        txt += '}'
        txt2 += 'return d;})('+txt+')'
        if rollOutDict:
            return txt2
        return txt

    def FunctionCall(self,fcalldef,**extraargs):

        
        args = fcalldef.args
        # create a qualified version of the function name (add a suffix specifying the number of arguments)
        # to use in template lookup
        kwargs = fcalldef.kwargs
        keyvalues = []
        dvtxt = None
        for key in kwargs:
            keyvalues.append((key,kwargs[key]))
        if len(keyvalues):
            dv = DictionaryValue(keyvalues)
            dvtxt = 'new Kwarg('+self.DictionaryValue(dv,ignoreFuncExpand=True)+')'
            self.addJslibSupport('Kwarg')
        fname = fcalldef.fname
        if not isinstance(fname,StringType):
            template = self.generate(fname)
        else:
            methodcall = ('targettxt' in extraargs)
            if not methodcall and self.module.getClassMountPoint(fname):
                fname = self.module.getClassMountPoint(fname)
            if not methodcall:
                fname = self.applyNamespace(fname)
            mname = ""
            if methodcall:
                path = self.attributeLookupPath(fcalldef.target)
                if path:
                    mname = path + "." + fcalldef.fname
            fname = self.module.applyAliases(fname)

            # search for a function mapping, starting with the qualified version
            qfname = fname + "." + str(len(args))     
            template = fname

            if methodcall:
                qfname = "." + qfname
                fname = "." + fname 

            lst = []
            if mname:
                lst.append(mname)
                lst.append(mname+"."+str(len(args)))
            lst.append(qfname)
            lst.append(fname)
            for name in lst:       
                if name in mappedFuncs:

                    dependencies = []

                    template = mappedFuncs[name]

                    if isinstance(template,tuple):
                        dependencies = template[1]
                        template = template[0]

                    for libfunc in dependencies:
                        self.addJslibSupport(libfunc)

                    if template == None:
                        raise BackendNotImplementedException("Function/Method:" + name)
                    else:
                        if mname ==  name or mname+"."+str(len(args)) == name:
                            del extraargs['targettxt']
                        break            

        argtxt = []
        for arg in args:
            argtxt.append(self.generate(arg))
        if dvtxt:
            argtxt.append(dvtxt)        
        txt = self.expand(template,argtxt,**extraargs)
        return txt

    def Lambda(self,ldef,**kwargs):
        self.pushScope(ldef)
        txt = 'function('
        for index in xrange(0,len(ldef.args)):
            if index > 0:
                txt += ','
            txt += ldef.args[index]
        txt += ') { return '
        txt += self.generate(ldef.body)
        txt += '; }'
        self.popScope()
        return txt

    def ListComprehension(self,compv,**kwargs):
        self.pushScope(compv)
        tmpname = self.genTmpVarName("comp")
        self.add("var "+tmpname + "= [];")
        self.nl()
        e = ExpressionStatement(MethodCall(VarName(tmpname),"append",[compv.expr],{}))     
        block = Block([e])
        generators = compv.generators
        generators.reverse()        
        for generator in generators:
            if generator.cond:
                i  = IfStatement([(generator.cond,block)],None)
                block = Block([i])
            if isinstance(generator.itr,FunctionCall) and generator.itr.fname == 'xrange':
                start = generator.itr.args[0]
                end = generator.itr.args[1]
                if len(generator.itr.args)==3:
                    step = generator.itr.args[2]
                else:
                    step = Literal(1)
                f = ForStatement(generator.target,start,end,step,block)
                block = Block([f])            
            else:
                f = ForInStatement(generator.target,generator.itr,block)
                block = Block([f])
        self.generate(block)
        self.popScope()
        return tmpname

    def ListValue(self,listv,**kwargs):
        txt = '['
        nr = len(listv.elements)
        for idx in xrange(0,nr):
            if idx > 0:
                txt += ','
            txt += self.generate(listv.elements[idx])
        txt += ']'
        return txt  

    def Literal(self,lit,**kwargs):   
        if isinstance(lit.value,bool):
            if lit.value == True:
                return 'true'
            else:
                return 'false'
        elif lit.value == None:
            return 'null'
        else:     
            return repr(lit.value)

    def MethodCall(self,mcalldef,**kwargs):
        target = ''
        path = self.attributeLookupPath(mcalldef.target)
        if path:
            path = path + "." + mcalldef.fname
            if path in class_aliases:
                target = class_aliases[path]
            
        if target == '':
            target = self.generate(mcalldef.target)
        txt = self.FunctionCall(mcalldef,targettxt=target)
        return txt

    def SliceOp(self,sop,**kwargs):
        txt = ''
        txt += self.generate(sop.target)
        txt += '.slice('
        if sop.lwb:
            txt += self.generate(sop.lwb)
        else:
            txt += '0'
        txt += ','
        if sop.upb:
            txt += self.generate(sop.upb)
        else:
            txt += self.generate(sop.target)+".length"
        # if sop.step:
        #     txt += ':'
        #     txt += self.generate(sop.step)
        txt += ')'
        return txt

    def UniOp(self,uop,**kwargs):
        txt = ''
        if not 'toplevel' in kwargs:
            txt += "("
        op = uop.op
        if op in unaryOps:
            op = unaryOps[op]
        else:
            raise BackendNotImplementedException("Unary Operation("+op+")")
        dependencies = []
        if isinstance(op,tuple):
            dependencies = op[1]
            op = op[0]
        for dependency in dependencies:
            self.addJslibSupport(dependency)
        txt += (op+' ')
        txt += self.generate(uop.arg)
        if not 'toplevel' in kwargs:
            txt += ")"
        return txt        

    def VarName(self,vdef,**kwargs):
        name = vdef.varname
        return self.module.getClassMountPoint(name) or self.module.getClassMountPoint(self.module.applyAliases(name)) or self.applyNamespace(self.module.applyAliases(name))


    # Statement handling
    # these methods do not return values but update the output program using the methods 

    def AssignmentStatement(self,adef,**kwargs):
        if isinstance(adef.target,SliceOp):
            self.AssignmentSliceStatement(adef,**kwargs)
            return
        class_variable = not self.hasOuterScope(FunctionDefinitionStatement)
        target = adef.target
        if not isinstance(target,AttributeLookup) and not class_variable:
            self.declare(adef.target)
            
        exprtxt = self.generate(adef.expr,toplevel=True) 
        if isinstance(target,ListValue):
            tmpv = self.genTmpVarName("list")
            self.declare(VarName(tmpv))
            self.add(tmpv+"="+exprtxt+";")
            self.nl()
            i = 0
            for el in target.elements:
                if isinstance(el,ListValue):
                    raise BackendException("No JS Generator handler for complex assignment", target, exprtxt)
                if not isinstance(el,AttributeLookup) and not class_variable:
                    self.declare(el)
                self.add(self.generate(el)+"="+tmpv+"["+str(i)+"];")
                self.nl()
                i+=1
        else:
            varname = self.generate(target,toplevel=True)                        
            self.add(varname)
            self.add('=')
            self.add(exprtxt)
            self.add(';')
       
    def AssignmentSliceStatement(self,adef,**kwargs):
        lwb = adef.target.lwb
        upb = adef.target.upb
        step = adef.target.step

        targettxt = self.generate(adef.target.target)
        exprtxt = self.generate(adef.expr)
        class_variable = not self.hasOuterScope(FunctionDefinitionStatement)        
        varname_s = self.genTmpVarName("slice")
        varname_l = self.genTmpVarName("loop")
        varname_c = self.genTmpVarName("counter")
        vartxt = "var "
        if class_variable:
            vartxt = ""
            self.applyNamespace(varname_s = self.genTmpVarName("slice"))
            self.applyNamespace(varname_l = self.genTmpVarName("loop"))
            self.applyNamespace(varname_c = self.genTmpVarName("counter"))
        if lwb:
            if isinstance(lwb,VarName) or isinstance(lwb,Literal):
                lwbtxt = self.generate(lwb)
            else:
                lwbtxt = self.genTmpVarName("lwb")
                self.add(vartxt+lwbtxt+"="+self.generate(lwb,toplevel=True)+";").nl()
        else:
            lwbtxt = "0"

        varname_u = self.genTmpVarName("upb")
        if upb:        
            self.add(vartxt+varname_u+"="+self.generate(upb,toplevel=True)+";").nl()
        else:
            self.add(vartxt+varname_u+"="+targettxt+".length;").nl()
        
        if step:
            if isinstance(step,VarName) or isinstance(step,Literal):
                steptxt = self.generate(step)
            else:
                steptxt = self.genTmpVarName("step")
                self.add(vartxt+steptxt+"="+self.generate(step,toplevel=True)+";").nl()
        else:
            steptxt = "1"
        
        self.add(vartxt+varname_s+"="+exprtxt+";").nl();
        self.add(vartxt+varname_l+";").nl()
        self.add(vartxt+varname_c+"=0;").nl()
        
        self.add("for("+varname_l+"="+lwbtxt+";"+varname_l+"<"+varname_u+";"+varname_l+"+="+steptxt+" ) {")        
        self += 1
        
        self.nl().add("if ( "+varname_c+" < "+varname_s+".length) {")
        self += 1
        self.nl()
        self.add(targettxt+"["+varname_l+"] = " + varname_s + "["+varname_c+"];")
        self -= 1
        self.nl().add("} else {")
        self += 1
        self.nl().add(targettxt+".splice("+varname_l+",1);")
        self.nl().add(varname_l+"--;")
        self.nl().add(varname_u+"--;")
        self -= 1
        self.nl().add("}").nl().add(varname_c+"++;")
        self -= 1
        self.nl()
        self.add("}").nl()
        self.add("while ( "+varname_c+" < "+varname_s+".length) {")
        self += 1
        self.nl().add(targettxt+".splice("+varname_l+",0," + varname_s + "["+varname_c+"]);")
        self.nl().add(varname_c+"++;")
        self.nl().add(varname_l+"++;")
        self -= 1
        self.nl().add("}")

    def AugmentedAssignmentStatement(self,adef,**kwargs):
        target = adef.target
        if not isinstance(target,AttributeLookup):
            self.declare(adef.target)
        vtxt = self.generate(target,toplevel=True)     
        etxt = self.generate(adef.expr,toplevel=True)
        op = adef.op
        if op in assignOps:
            op = assignOps[op]
        else:
            raise BackendNotImplementedException("Augmented Assignment Operation("+op+")")
        dependencies = []
        if isinstance(op,tuple):
            dependencies = op[1]
            op = op[0]
        for dependency in dependencies:
            self.addJslibSupport(dependency)
        txt = self.expand(op,[vtxt,etxt])
        self.add(txt+";")

    def Block(self,block,**kwargs):
        self.pushScope(block)
        if not 'toplevel' in kwargs:
            self.openBlock()
        if 'extras' in kwargs:
            for e in kwargs['extras']:
                self.add(e)
                self.nl()
        for a in xrange(0,len(block.statements)):
            statement = block.statements[a]                        
            self.generate(statement)
            if a != len(block.statements)-1:
                self.nl()
        if not 'toplevel' in kwargs:
            self.closeBlock()
        self.popScope()

    def BreakStatement(self,breakdef,**kwargs):
        self.add('break;')

    def ClassDefinitionStatementStubGenericBody(self,memberfn,namespace,fname,**kwargs):
        instname = "this"
        if 'instname' in kwargs:
            instname = kwargs['instname']
        constructor = False
        if 'constructor' in kwargs:
            constructor = kwargs['constructor']
        btxts = []
        if 'staticmethod' in memberfn.decorators:
            btxts.append("args = [];")
        else:
            btxts.append("args = ["+instname+"];")
        btxts.append("for(var a=0;a<arguments.length;a++) {")
        btxts.append(self.indentstr+"args.push(arguments[a]);")
        btxts.append("}")
        retline = ""
        if not constructor:
            retline += "return "
        retline += self.applyNamespace(fname,namespace=namespace)+".apply(null,args);"
        btxts.append(retline)
        return btxts

    def ClassDefinitionStatementStub(self,memberfn,namespace,fname,**kwargs):
        objname = "self"
        if 'objname' in kwargs:
            objname = kwargs['objname']
        instname = "this"
        if 'instname' in kwargs:
            instname = kwargs['instname']
        isstatic = False
        if 'staticmethod' in memberfn.decorators:
            isstatic = True
        if memberfn.kwarg != None or memberfn.vararg != None:
            factxts = []
            factxts.append(objname+"."+fname+" = function() {")
            btxts = self.ClassDefinitionStatementStubGenericBody(memberfn,namespace,fname,instname=instname)
            for btxt in btxts:
                factxts.append(self.indentstr+btxt)
            factxts.append("}")
            return factxts
        else:
            factxt = objname+"."+fname+ " = function("
            argtxt = ""
            startarg=1
            if isstatic:
                startarg=0
            for idx in xrange(startarg,len(memberfn.argnames)):
                if idx > 1: 
                    argtxt += ","
                argtxt += pj_var.get(memberfn.argnames[idx],memberfn.argnames[idx])


            factxt += argtxt
            factxt += ") { return " + self.applyNamespace(fname,namespace=namespace) 
            if isstatic:
                factxt += "("+argtxt+")"
            else:
                if argtxt != "":
                    argtxt = ","+argtxt
                factxt += "("+instname+argtxt+")"
            factxt += "; }"
            return [factxt]            

    def ClassDefinitionStatement(self,cdef,**kwargs):

        self.pushScope(cdef)
        decorators = []
        ctrargs = []
        ctrvararg = None
        ctrkwarg = None
        if cdef.constructor:
            decorators = cdef.constructor.decorators
            ctrargs = cdef.constructor.argnames[1:]
            ctrvararg = cdef.constructor.vararg
            ctrkwarg = cdef.constructor.kwarg
        facbody = []
        facbody.append(Verbatim("if (arguments.length==1 && arguments[0] == undefined) { return; }"))
        facbody.append(Verbatim("var self = new "+self.applyNamespace(cdef.cname)+"(undefined);"))
        # call the $self method
        if True: 
            if cdef.constructor and (cdef.constructor.kwarg != None or cdef.constructor.vararg != None):
                btxts = self.ClassDefinitionStatementStubGenericBody(cdef.constructor,
                                                            cdef.cname,self.applyNamespace("$self"),instname='self',constructor=True)
                for btxt in btxts:
                    facbody.append(Verbatim(btxt))    
            else:
                ctrcall = ""
                ctrcall += self.applyNamespace("$self")
                ctrcall += "(self);"
                facbody.append(Verbatim(ctrcall))
        # if the class has a constructor, need to call it towards the end of the factory function
        if cdef.constructor:              
            if cdef.constructor.kwarg != None or cdef.constructor.vararg != None:
                btxts = self.ClassDefinitionStatementStubGenericBody(cdef.constructor,
                                                            cdef.cname,cdef.constructor.fname,instname='self',constructor=True)
                for btxt in btxts:
                    facbody.append(Verbatim(btxt))    
            else:
                ctrcall = ""
                ctrcall += self.applyNamespace(cdef.constructor.fname)
                ctrcall += "(self"
                argtxt = ""
                for idx in xrange(1,len(cdef.constructor.argnames)):
                    if idx > 1: 
                        argtxt += ","
                    argtxt += pj_var.get(cdef.constructor.argnames[idx],cdef.constructor.argnames[idx])
                if argtxt != "":
                    argtxt = ","+argtxt
                ctrcall += argtxt + ");"
                facbody.append(Verbatim(ctrcall))
        
        facbody.append(Verbatim("return self;"))            
        self.popScope()        

        # now create a dummy FunctionDefinitionStatement to generate the factory function
        facfn = FunctionDefinitionStatement(cdef.cname)
        
        facfn.configure(decorators,
                    ctrargs,
                    [],
                    ctrvararg,
                    ctrkwarg,
                    Block(facbody))
        self.generate(facfn)
        self.nl()
        self.nl()
        self.pushScope(cdef)

        # FIXME - should be all the superclasses, not just bases
        self.generate(Verbatim(self.applyNamespace("$classess")+"=["+ ",".join(map(lambda b: self.applyNamespace(b), cdef.bases)) + "];"))
        self.nl()

        self.ClassSelfMethod(cdef,**kwargs)

        # generate the defintion for the class __init__ constructor (if it exists)
        if cdef.constructor:
            # self.generate(cdef.constructor,class_owner=cdef.cname)
            self.generate(cdef.constructor)
            self.nl()

        # generate definitions for all other member and static class functions
        fns = cdef.memberfns()
        for (fname, classname,memberfn) in fns:
            
            if classname==cdef.getClassNamespace():
                # only generate functions which are defined on this class (not inherited ones)
                self.generate(memberfn)
                self.nl()
            else:
                # for inherited, static methods need to note an alias for rewriting callers
                if 'staticmethod' in memberfn.decorators:
                    key = cdef.getClassNamespace()+"."+fname
                    alias = classname
                    class_aliases[key] = alias
                    self.add( "/* "+key+"->"+alias+" */" )
                    self.nl()

        # generate static class variables now
        for (target,expr) in cdef.staticmembervars:
            a = AssignmentStatement(target,expr)
            self.generate(a)
            self.nl()
        #self.ClassSuperMethod(cdef,**kwargs)
        self.popScope()


    def ClassSelfMethod(self,cdef,**kwargs):
        namespace = cdef.getClassNamespace()
        decorators = []
        ctrargs = ["self"]
        ctrvararg = None
        ctrkwarg = None
        facbody = []
        # call all the $self methods of all the base classes
        for base in cdef.bases:
            txt = "if ("+self.applyNamespace(base) + ".$self) {" + self.applyNamespace(base) + ".$self(self);}"
            facbody.append(Verbatim(txt))
        self.setNamespace(namespace)
        facbody.append(Verbatim("self.$classess = " + self.applyNamespace("$classess")))
        facbody.append(Verbatim("self.$new = "+self.applyNamespace(cdef.cname)+";"))
        # hook up member functions as properties of the class instance
        fns = cdef.memberfns()
        for (fname, ns, memberfn) in fns:
            stubs = self.ClassDefinitionStatementStub(memberfn,ns,fname)
            for stub in stubs:
                facbody.append(Verbatim(stub))

        # hook up factory functions for inner classes as properties of the class instance
        # FIXME need to do this recursively?
        innerclasses = cdef.innerclasslist()
        for (innerclass,innernamespace) in innerclasses:
            txt = "self."+innerclass.cname+"="+innernamespace+"."+innerclass.cname+";"
            facbody.append(Verbatim(txt))

        # generate static class variables now
        for (target,expr) in cdef.staticmembervars:
            walker = VarNameWalker()
            target.walk(walker)
            varnames = walker.getVarNames()
            declares = []
            for varname in varnames:
                txt = "self."+varname+"="+self.applyNamespace(varname)+";"
                facbody.append(Verbatim(txt))


        # factory function defined
        # now create a dummy FunctionDefinitionStatement to generate the self function
        facfn = FunctionDefinitionStatement("$self")
        
        facfn.configure(decorators,
                    ctrargs,
                    [],
                    ctrvararg,
                    ctrkwarg,
                    Block(facbody))
        self.generate(facfn)
        self.nl()

    # this function overrides the self variable's functions with the parent's.
    # this could have unfortunate consequences. no longer supported.
    def ClassSuperMethod(self,cdef,**kwargs):
        namespace = cdef.getClassNamespace()
        decorators = []
        ctrargs = ["self"]
        ctrvararg = None
        ctrkwarg = None
        facbody = []
        facbody.append(Verbatim("this.self = self;"));
        fns = cdef.memberfns(True)
        for fname in fns:
            (ns,memberfn) = fns[fname]            
            stubs = self.ClassDefinitionStatementStub(memberfn,ns,fname,objname='this',instname='this.self')
            for stub in stubs:
                facbody.append(Verbatim(stub))
        facbody.append(Verbatim("return this;"));
        facfn = FunctionDefinitionStatement("super")
        
        facfn.configure(decorators,
                    ctrargs,
                    [],
                    ctrvararg,
                    ctrkwarg,
                    Block(facbody))
        self.generate(facfn)
        self.nl()


    def ContinueStatement(self,continuedef,**kwargs):
        self.add('continue;')

    def DeclareStatement(self,ddef):
        if len(ddef.declarevars):
            self.add("var ");
            for index in xrange(0,len(ddef.declarevars)):
                if index > 0:
                    self.add(",")
                self.add(pj_var.get(ddef.declarevars[index], ddef.declarevars[index]))
            self.add(";")

    def DeleteStatement(self,ddef):
        if isinstance(ddef.target,SliceOp):
            self.generate(AssignmentStatement(ddef.target,ListValue([])))
        elif isinstance(ddef.target,BinaryOp) and ddef.target.op == '[]':
            lefttxt = self.generate(ddef.target.left)
            righttxt = self.generate(ddef.target.right)
            self.add("if ("+lefttxt+" instanceof Array) {")
            self += 1
            self.nl().add(lefttxt + ".splice(" + righttxt + ",1);")
            self -= 1
            self.nl().add("} else {")
            self += 1
            self.nl().add("delete "+lefttxt+"["+righttxt+"]")
            self -= 1
            self.nl().add("}")
        else:
            targettxt = self.generate(ddef.target,toplevel=True)       
            self.add("delete " + targettxt);        

    def EmptyStatement(self,edef,**kwargs):
        # add a comment to make the resulting javascript a little more readable
        self.add("/* pass */")

    def ExceptionHandlerStatement(self,hdef,**kwargs):
        self.pushScope(hdef)
        e = []
        catchvar = self.getCatchVar()
        index = kwargs['handler_index']  
        if hdef.ename:      
            if hdef.etype:
                if index == 0:
                    self.add("if ")
                else:
                    self.add(" else if ")
                self.add("(" + catchvar + " instanceof " + hdef.etype + ")")
        
            if hdef.ename != catchvar:
                e.append("var "+hdef.ename+"="+catchvar+";")
        else:
            if index > 0:
                self.add(" else ")
        self.generate(hdef.ebody,extras=e)    
        self.popScope()

    def ExpressionStatement(self,edef,**kwargs):
        self.add(self.generate(edef.expr,toplevel=True))
        self.add(';')        

    def ForStatement(self,fordef,**kwargs):
        self.pushScope(fordef)
        self.declare(fordef.varname)
        lwbtxt = self.generate(fordef.lwb) 
        upbtxt = self.generate(fordef.upb) 
        if lwbtxt == upbtxt:
            lwbtxt = "0"
        steptxt = self.generate(fordef.step)
        varname = self.generate(fordef.varname)  
        self.add('for(')
        self.add(varname+'='+lwbtxt+';')
        self.add(varname+'<'+upbtxt+';')
        self.add(varname +'+=' + steptxt +')')
        self.generate(fordef.block)
        self.popScope()

    def ForInStatement(self,fordef,**kwargs):
        self.pushScope(fordef)
        tmpv = None
        self.addJslibSupport('Generator')
        self.declare(fordef.target)
        if self.inYieldFn:
            self.add(self.JSYieldGuard(fordef))
            self.openBlock()
            tmpv = self.genTmpVarName("generator")
            self.add('var '+tmpv+';')
            self.nl()
            self.add("if (_yieldobj."+tmpv+") { " + tmpv + " = " + "_yieldobj."+tmpv+";}")
            self.nl()
            self.add("else")
            self.openBlock()
            #tmp = self.genTmpVarName(self.module.name+"_container")
            #a = AssignmentStatement(VarName(tmp),fordef.container)
            #self.generate(a)
            #self.nl();
            self.add(tmpv + " =  new $pj.Generator("+self.generate(fordef.container)+");")
            self.nl()
            self.add("_yieldobj."+tmpv+" = "+ tmpv+";")
            self.closeBlock()
            self.nl();
        else:
            #tmp = self.genTmpVarName(self.module.name+"_container")
            #a = AssignmentStatement(VarName(tmp),fordef.container)
            #self.generate(a)
            #self.nl();
            tmpv = self.genTmpVarName("generator")
            self.add('var '+tmpv+' = new $pj.Generator('+self.generate(fordef.container)+');')
            self.nl()   


        e = []

        if isinstance(fordef.target,ListValue):
            varname = self.genTmpVarName("loop")
            txt = self.generate(fordef.target)
            txt += "="
            txt += varname
            txt += ";"
            e.append(txt)
        else:
            varname = self.generate(fordef.target)
        
        self.add('for(')                    
        self.add(varname+'='+tmpv+'.nextValue();'+tmpv+'.hadMore();'+varname+'='+tmpv+'.nextValue())')
        self.generate(fordef.block,extras=e)
        self.popScope()
        if self.inYieldFn:
            self.nl()
            self.add("_yieldobj._yeldState = " + str(fordef.yieldState + self.yieldState + 1)+";")
            self.nl()
            self.add("_yieldobj."+tmpv+" = undefined;")
            self.closeBlock()

    def FunctionDefinitionStatement(self,funcdef,**kwargs):
        if funcdef.yieldScope:
            self.inYieldFn=True
        self.pushScope(funcdef)
        name = funcdef.fname                   
        nsname = self.applyNamespace(name)
        
        txt =  nsname + " = function("            
        argc = len(funcdef.argnames)
        for a in xrange(0,argc):
            if a>0:
               txt += ","
            argname=pj_var.get(funcdef.argnames[a],funcdef.argnames[a])
           
            txt+=argname
        txt += ") "
        self.add(txt)
        e = []

        if len(funcdef.argdefaults):
            kwarg = self.genTmpVarName()
            offset = len(funcdef.argnames) - len(funcdef.argdefaults)
            e += ['var ' + kwarg + ';']
            for di in xrange(0,len(funcdef.argdefaults)):
                argname = pj_var.get(funcdef.argnames[di+offset],funcdef.argnames[di+offset])
                e += ['if ('+argname+' == undefined) {']
                e += ['   '+argname+'=(('+kwarg+' && '+kwarg+'.'+argname+' != undefined) ? '+kwarg+'.'+argname+' : ' + self.generate(funcdef.argdefaults[di],toplevel=True)+');']
                e += ['} else if ('+argname+' instanceof Kwarg) { ']        
                e += ['   '+kwarg + '= '+argname+'.getDict(); ']
                e += ['   '+argname+'=(('+kwarg+' && '+kwarg+'.'+argname+' != undefined) ? '+kwarg+'.'+argname+' : ' + self.generate(funcdef.argdefaults[di],toplevel=True)+');']
                e += ['} ']        

        if funcdef.kwarg or funcdef.vararg:
            tmpv_len = self.genTmpVarName()
            e += ['var ' + tmpv_len + '= arguments.length;']
    
        if funcdef.kwarg:        
            self.addJslibSupport('Kwarg')
            tmpv_lastarg = self.genTmpVarName()
            e += ['var ' + tmpv_lastarg + '= arguments[arguments.length-1];']
            e += ['var ' + funcdef.kwarg + ' = {};']
            e += ['if (' + tmpv_lastarg + ' instanceof Kwarg) {']
            e += ['    ' + funcdef.kwarg + ' = ' + tmpv_lastarg + '.getDict();']
            e += ['    ' + tmpv_len + '--;']
            e += [' } ']      
        if funcdef.vararg:
            tmpv = self.genTmpVarName()
            e += ['var '+funcdef.vararg + '= [];']
            e += ['for('+tmpv+'='+str(argc)+';'+tmpv+'<'+tmpv_len+';'+tmpv+'++) {']
            e += ['    ' + funcdef.vararg + '.push(arguments['+tmpv+']);']
            e += ['}'] 
        self.generate(funcdef.block,extras=e)
        self.popScope()
        self.inYieldFn=False        

    def GlobalStatement(self,gdef,**kwargs):
        pass
        # self.addGlobal(gdef.varname)

    def IfStatement(self,ifdef,**kwargs):
        self.pushScope(ifdef)
        idx = 0
        for test in ifdef.tests:
            cond, block = test
            if idx == 0:
                self.add("if (")
            else:
                self.add("else if (")
            self.add(self.generate(cond,toplevel=True))
            self.add(")")
            self.generate(block)
        self.popScope()
        if ifdef.elseblock:
            self.add("else ")
            self.pushScope(ifdef.elseblock)
            self.generate(ifdef.elseblock)            
            self.popScope()

    def Module(self,mdef,**kwargs):
        # add loading code
        #self.add("LazyLoad.js('"+mdef.name+".js');")
        #self.nl()
        if mdef.namespace != self.namespace and mdef.namespace not in JavascriptBackend.loaded_modules:
            JavascriptBackend.loaded_modules.append(mdef.namespace)            
            self.module_depends.append(mdef.namespace)
            jb = JavascriptBackend(mdef.namespace.strip("/").replace(".","/")+".py", homepath=os.getcwd())
            jb.generate(mdef)
            return

        if "." in self.namespace:
            self.curr_file = open(os.path.join(self.homepath, self.namespace.replace(".", "/")+".js"), "w")
        else:
            self.curr_file = open(self.namespace+".js", "w")

        self.pushScope(mdef)
        self.module = mdef
        header = "// generated by pj from "+mdef.path + " last updated: " + time.ctime(os.path.getmtime(mdef.path)) +"\n"
        if mainpath == self.path:
            header+= "// dependencies: " + " ".join(loaded_paths[1:]) + "\n"
        #self.createNamespace(self.namespace)
        self.add(header)
        self.add("var " + mdef.name +" = ($pj.loaded_modules.indexOf("+ mdef.name + ")!= -1) ? "+ mdef.name + " : (function ("+ mdef.name + ") { ")
        self.nl()
        self.add("var __name__ = ($pj.main_module == '"+ mdef.name + "') ? '__main__' : '__"+ mdef.name + "__';")
        self.nl()
        self.generate(mdef.code,toplevel=True)
        self.nl()
        if self.isLocal("$main"):
            self.add(self.applyNamespace("$main")+"();");
            self.nl()
        self.add("$pj.loaded_modules.push("+ mdef.name + ");")
        self.nl()
        self.add("return "+ mdef.name + ";")
        self.nl()
        self.add("}({}));")
        self.curr_file.write(self.code)
        self.popScope()
        self.curr_file.close()

    def PrintStatement(self,printdef,**kwargs):
        self.add("$pj.print(")
        for a in xrange(0,len(printdef.values)):
            if a>0:
                self.add('+ " " +')
            #self.add('String(')
            self.add(self.generate(printdef.values[a]))
            #self.add(')')
        self.add(');')

    def RaiseStatement(self,rdef,**kwargs):
        self.add("throw ")
        if rdef.rtype:
            self.add(self.generate(rdef.rtype))
            if rdef.robj:
                self.add("(")
                self.add(self.generate(rdef.robj))
                self.add(")")
        else:
            catchvar = self.getCatchVar()
            self.add(catchvar)
        self.add(";")

    def ReturnStatement(self,retdef,**kwargs):
        self.add('return')
        if retdef.value:
            self.add(' ')
            self.add(self.generate(retdef.value))
        self.add(';')

    def YieldStatement(self,retdef,**kwargs):
        txt = None
        if self.hasOuterScope(ForStatement):
            self.incrYieldState()
            txt = self.JSYieldGuard (retdef) + '{ return ' + self.generate(retdef.value) + '}'
        else:
            txt = self.JSYieldGuard (retdef) + '{ _yieldobj._yieldState++; return ' + self.generate(retdef.value) + '}'            
        self.incrYieldState()
        return txt

    def TryStatement(self,trydef,**kwargs):
        self.pushScope(trydef)
        self.add("try")
        self.generate(trydef.body)
        self.popScope()
        if len(trydef.handlers)>0:
            self.add("catch")
            catchvar = None
            if len(trydef.handlers)==1:
                catchvar = trydef.handlers[0].ename
            if catchvar == None:
                catchvar = self.genTmpVarName("ex")
            self.pushCatchVar(catchvar)
            self.add("("+catchvar+")")
            catchall = False
            if len(trydef.handlers)==1 and trydef.handlers[0].ename == None:
                catchall = True
            if not catchall:
                self.openBlock()        
            for idx in xrange(0,len(trydef.handlers)):
                self.pushScope(trydef.handlers[idx])
                self.generate(trydef.handlers[idx],handler_index=idx)
                self.popScope()
            if not catchall:
                self.closeBlock()
            self.popCatchVar()
        if trydef.final:
            self.add("finally")
            self.pushScope(trydef.final)
            self.generate(trydef.final)
            self.popScope()

    def WhileStatement(self,whiledef,**kwargs):
        self.pushScope(whiledef)
        self.add('while(')
        self.add(self.generate(whiledef.cond,toplevel=True))
        self.add(')')
        self.generate(whiledef.block)                
        self.popScope()

    def translate_escaped_names(self, txt):
        """ escape replace names
        """
        l = escaped_subst.split(txt)
        txt = l[0]
        for i in xrange(1, len(l)-1, 2):
            varname = l[i].strip()
            if varname.startswith('!'):
                    txt += varname[1:]
            else:
                substname = self.module.getClassMountPoint(varname) or self.module.getClassMountPoint(self.module.applyAliases(varname)) or self.applyNamespace(self.module.applyAliases(varname))
                txt += substname
            txt += l[i+1]
        return txt

    def Verbatim(self,vdef,**kwargs):
        text = vdef.text
        if "@{{" in text:
            text = self.translate_escaped_names(text)
        if vdef.exp:
            return text.strip(";")            
        if "\n" in text:
            textlines = text.split('\n')
            for textline in textlines:
                self.nl()
                self.add(textline)
        else:
            self.add(text)


    # Common

    def generate(self,code,**kwargs): 
        name = code.__class__.__name__
        if not hasattr(self,name):
            raise BackendException("No JS Generator handler for object: "+name)
        return getattr(self,code.__class__.__name__)(code,**kwargs)

    def declare(self,target):
        walker = VarNameWalker()
        target.walk(walker)
        varnames = walker.getVarNames()
        declares = []
        for varname in varnames:
            if not self.isGlobal(varname) and not self.isLocal(varname):
                declares.append(varname)
                self.addGlobal(varname)
        if declares:
            decl = DeclareStatement(declares)
            self.generate(decl)
            self.nl()      

    def nl(self):
        self.add('\n')
        for i in xrange(0,self.indent):
            self.add(self.indentstr)
        return self
        
    def add(self,str):
        if str:
            self.code += str
        return self

    def __add__(self,num):
        self.indent += num 
        return self      

    def openBlock(self):
        self.add(" {")
        self += 1
        self.nl()
        return self

    def closeBlock(self):
        self -= 1
        self.nl()
        self.add("}")
        return self

    def __sub__(self,num):
        self.indent -= num
        return self


    def expand(self,template,parameters,**kwargs):
        parameters = map(lambda p: pj_var.get(p,p), parameters)
        # check to see if there is a target object (or class) associated with the call
        targettxt = ''
        if 'targettxt' in kwargs:
            targettxt = kwargs['targettxt']        
        # create the default placeholders string eg (%1,%2,%3) if there are 3 parameters
        placeholders = ""
        for index in xrange(0,len(parameters)):
                if index > 0:
                    placeholders += ','
                placeholders += '%'
                placeholders += str(index+1)
        # create the template to expand
        if template.find('%') == -1 and template.find('(') in (0, -1):
            template += '('+placeholders+')'
        elif template.find('%*'):
            template = template.replace('%*',placeholders)
        # compile a list of the position of each placeholder %1, %2, ... and its index in the template
        matches = []
        startindex = 1
        if targettxt != '':
            startindex = 0
        for index in xrange(startindex,len(parameters)+1):
            placeholder = '%'+str(index)
            pos = 0
            while pos > -1:
                pos = template.find(placeholder,pos)
                if pos > -1:
                    matches.append((pos,index-1))
                    pos += 1
        # sort the matches into reverse order (ones at the end of the template occuring earlier)
        def matchsort(x,y):
            if x[0] < y[0]:
                return 1
            if x[0] == y[0]:
                return 0
            return -11
        matches.sort(matchsort)
        # convert the template from a string to a list ready to manipulate
        expansion = list(template)
        # work backwards through the string swapping placeholders for parameters
        maptarget=False        
        for (pos,index) in matches:
            if index >= 0:
                expansion[pos:pos+2] = list(parameters[index])
            else:
                # found a %0 to match
                expansion[pos:pos+2] = targettxt
                # note that we are switching from a method call to a function call
                # with the target mapped to a parameter
                maptarget=True                                
        # convert back to a string and return
        txt = ''
        if targettxt != '' and not maptarget:
            # make an instance call or a static function call (if the target is a class name)
            txt += targettxt
            txt += "."
        txt += ''.join(expansion)
        return txt

    def unpackListValue(self,target,varname,assignments):
        if isinstance(target,ListValue):
            for idx in xrange(0,len(target.elements)):                                                
                self.unpackListValue(target.elements[idx],varname+"["+str(idx)+"]",assignments)
        elif isinstance(target,VarName):
            txt = ""
            # if target.isdecl:
            txt +=  "var "
            txt += self.generate(target)
            txt += "="
            txt += varname
            txt += ";"
            assignments.append(txt)
        elif isinstance(target,AttributeLookup):
            txt = self.generate(target)
            txt += "="
            txt += varname
            txt += ";"
        else:
            assert False                
            
    def insertDependency(self,line):
        self.dependencies = [line] + self.dependencies

    def generateDependencies(self):
        for dependency in self.dependencies:
            self.add(dependency)
            self.nl()
        self.dependencies = []
   
    def addJslibSupport(self,package):
        self.jslib_support[package] = True

    def genTmpVarName(self,prefix=''):
        self.varcount += 1
        return prefix+"_pj_"+str(self.varcount)

def create_namespace(module,skiplast=False):
    return ""
    txt = ""
    names= module.split(".")
    global mdict
    path = ""
    max = len(names)
    if skiplast:
        max -= 1
    for x in xrange(0,max):
        if x > 0:
            path += "."
        path = path+names[x]
        if path not in mdict:
            if x == 0:
                txt += "var "
            txt += path
            txt += " = {};\n"
            mdict[path] = ""
    mdict[module] = ""
    return txt                    

mainpath = ""        
# write a module
def jswrite(code,pypath):
    global mdict
    mdict.clear()
    class_aliases.clear()
    jb = JavascriptBackend(pypath, os.getcwd())
    jb.generate(code)

        


global_modules = ["sys", "copy", "os", "re", "string", "math", "types", "random", "time" , "gc"] # todo 
#, "htmlentitydefs", "operator", "datetime", "sets", "urllib", "urlparse", "time", "struct", "socket", "md5", "ipaddr", "getopt", "csv", "cgi", "binascii", "base64", "StringIO", "pj"
global initial_module_dir
initial_module_dir = ''

class FrontendException(Exception):

    def __init__(self,detail,lineno,path):
        self.detail = detail
        self.lineno = lineno
        self.path = path

    def __str__(self):
        return "Cannot convert python code at line "+str(self.lineno)+": "+ self.detail + ":" + str(self.path)


class FrontendInternalException(FrontendException):

    def __init__(self,detail,linenom,path):
        FrontendException.__init__(self,detail,lineno,path)

    def __str__(self):
        return "Python parser internal error "+str(self.lineno)+": "+ self.details + ":" + str(self.path)


def pyread(path,module=None):
    if path not in loaded_paths:
        loaded_paths.append(path)
    testf = None
    try:
        testf =  open(path.replace(".py", ".js"),"r")
    except:
        pass
    if testf:
        line = testf.readline()
        if "last updated:" in line and line.split("last updated:")[-1].strip() == str(time.ctime(os.path.getmtime(path))):
            print "skipping file. no changes detected: "+path  
            line = testf.readline()
            modules=[]
            if "dependencies:" in line:
                modpaths = line.split("dependencies:")[-1].strip().split()
                for modpath in modpaths:
                    code = pyread(modpath)
                    if code: modules.extend(code)
            return modules
    print "parsing: "+path
    if module == None:
        namespace =  path.split("/")[-1].replace(".py", "")
        ppath= "/".join(path.split("/")[:-1])
        module = (namespace,path,namespace, [])
        (mdir,mfile) = os.path.split(path)
        global initial_module_dir
        initial_module_dir = mdir
    file = open(path, "r")
    contents = file.read()
    gv = GenVisitor(module[0],module[1],module[2])
    return [gv.parse(contents)]

def makeMainFile(homepath, module_name, module_namespace):
    f = open(os.path.join(homepath, module_name+"_main.html"), "w")
    f.write('<SCRIPT language="JavaScript">\n')
    f.write(pj_lib)
    f.write('\n$pj.main_module="'+module_name+'";\n')
    f.write('</SCRIPT>\n')
    seen = []
    for module in loaded_paths[1:]:
        if module not in seen:
            seen.append(module)
            f.write('<SCRIPT language="JavaScript" SRC="'+module.replace(".py",".js")+'"></SCRIPT>\n')
    module = loaded_paths[0]
    f.write('<SCRIPT language="JavaScript" SRC="'+module.replace(".py",".js")+'"></SCRIPT>\n')
    f.close()

if __name__ == '__main__':
    debug = False
    args = sys.argv[1:]
    outputdir = None
    outputfiles = []
    doDir = False
    for i in xrange(len(args)):
        if "-debug" ==  args[i]:
            debug = True
            args[i] = None
            
        if "-out" == args[i]:
            outputdir = args[i+1]
            args[i]=None
            args[i+1]=None
        if "-dir" == args[i]:
            doDir = True
            args[i]=None
    homepath = os.getcwd()
    for argfile in  args:
        if argfile == None:
            continue
        if not mainpath:
            mainpath = argfile 
        if doDir:
            for argfile2 in os.listdir(os.path.join(homepath, argfile)):
                argfile2 = argfile+"/"+argfile2
                outputfiles.append(argfile2)
                codes = pyread(argfile2)
                jb = JavascriptBackend(argfile, os.getcwd())
                mdict.clear()
                class_aliases.clear()
                for code in codes:
                    jb.generate(code)
        else:
            outputfiles.append(argfile)
            codes = pyread(argfile)
            jb = JavascriptBackend(argfile, os.getcwd())
            mdict.clear()
            class_aliases.clear()
            for code in codes:
                jb.generate(code)
    mainPathArr = mainpath.replace(".py", "").split("/")
    mainPathArr[-1] = "pj.js"
    pj = "/".join(mainPathArr)
    outputfiles.append(pj)
    f = open(os.path.join(homepath, pj), "w")
    print "generating", os.path.join(homepath, pj)
    f.write(pj_lib)
    f.close()
    # doesn't work. doesn't copy all dependencies that have changed. 
    if outputdir:
        for argfile in outputfiles:
            cp= "cp " + argfile.replace(".py", ".js") + " " + outputdir
            os.system(cp)
            print cp


