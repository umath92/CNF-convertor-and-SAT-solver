"""
The programs gives the SAT satisfiability of a clause. It reads the clauses from CNF_sentences.txt and
prints the corresponding output to CNF_satisfiability.txt
"""

import sys

global mod
mod=[]

# gets the symbols out of the given clause.
def Make_Symbol(conjunct):
    if not isinstance(conjunct,list):
        return [conjunct]
    elif (conjunct[0]=='and'):
        lst=[]
        for x in range(1,len(conjunct)):
            lst=lst+Make_Symbol(conjunct[x])
        return lst
    elif (conjunct[0]=='or'):
        lst=[]
        for x in range(1,len(conjunct)):
            lst=lst+Make_Symbol(conjunct[x])
        return lst
    elif (conjunct[0]=='not'):
        return Make_Symbol(conjunct[1])

# this functions checks if the clause is satifiable or not.
def Check_Clause(clauses,symbol,model):
    if not isinstance(clauses,list):
        for [x,y] in model:
            if x==clauses:
                return y
        else:
            return False
    if (len(clauses)==0):
        return True
    elif (clauses[0]=='and'):
        f=True
        for x in range(1,len(clauses)):
            f=f and Check_Clause(clauses[x],symbol,model)

        return f
    elif (clauses[0]=='or'):
        f=False
        for x in range(1,len(clauses)):
            f=f or Check_Clause(clauses[x],symbol,model)

        return f
    elif (clauses[0]=='not'):
        return (not Check_Clause(clauses[1],symbol,model))
    else:
        return True

def Check_Clause_False(clauses,symbol,model):
    if not isinstance(clauses,list):
        for [x,y] in model:
            if x==clauses:
                return y
        else:
            return False
    elif (clauses[0]=='and'):
        f=True
        for x in range(1,len(clauses)):
            f=f and Check_Clause_False(clauses[x],symbol,model)
        return f
    elif (clauses[0]=='or'):
        f=False
        for x in range(1,len(clauses)):
            f=f or Check_Clause_False(clauses[x],symbol,model)
        return f
    elif (clauses[0]=='not'):
        return (not Check_Clause_False(clauses[1],symbol,model))
    else:
        return False

# the fucntion implements to DPLL algorithm to get the SAT satisfiability of the clause
def DPLL(clauses, symbol, model):
    #print clauses
    global mod
    flag2=True
    for x in symbol:
        flag=False
        for [y,z] in model:
            if(y==x):
                flag=True
                break
        flag2=flag and flag2
    clauses=Check_all(clauses)

    if(Check_single(clauses)[0]==True):
            clauses=Check_single(clauses)[1]
    if (Empty_clause(clauses)==True):
        return False
    print clauses
    if flag2==True:
        if(Check_Clause(clauses,symbol,model)==True):
            mod=list(model)
            return True
        #print clauses
        if(clauses[0]=='and'):
            for x in range(1,len(clauses)):
                if(Check_Clause(clauses[x],symbol,model)==False):
                    return False
    else:
        ########################## Pure Symbol ###############################
        for x in symbol:
            dummy=False
            for [y,z] in model:
                if(y==x):
                    dummy=True
                    break
        if(dummy==False): 
            clauses= Check_all(clauses)
            var =Check_occurances_single(clauses,x)
            if(var!=Check_occurances_notSingle(clauses,x)):
                if(var==True):
                    clau=Remove_P2(clauses,x)
                    clau=Check_all(clauses)
                    if(Empty_clause(clau)==True):
                        return False
                    symbol.remove(x)
                    model.append([x,True])
                    return DPLL(clau,symbol,model)
                else:
                    clau=Remove_NotP2(clauses,x)
                    clau=Check_all(clau)
                    if(Empty_clause(clau)==True):
                        return False
                    symbol.remove(x)
                    model.append([x,False])
                    return DPLL(clau,symbol,model)
            
        ########################## Pure Symbol ###############################
        ########################## Unit Clause ###############################
        for x in symbol:
            clauses= Check_all(clauses)
            #######################################
            if(Check_singel_Clause(clauses,x)==True):
                clau=Remove_clauses(clauses,x)
                clau=Remove_NotP2(clau,x)
                clau=Check_all(clau)
                symbol.remove(x)
                model.append([x,True])
                if(Empty_clause(clau)==True):
                    return False
                return DPLL(clau,symbol,model)
            if(Check_singel_notClause(clauses,x)==True):
                clau=Remove_Notclauses(clauses,x)
                clau=Remove_P2(clau,x)
                clau=Check_all(clau)
                symbol.remove(x)
                model.append([x,False])
                if(Empty_clause(clau)==True):
                    return False
                return DPLL(clau,symbol,model)
        ########################## Unit Clause ###############################
        ########################## Splitting rule ###############################
        sym1=symbol[:]
        sym2=symbol[:]
        s1=sym1.pop()
        s2=sym2.pop()
        model1=model[:]
        model2=model[:]
        model1.append([s1,True])
        clau1=Remove_clauses(clauses,s1)
        clau1=Remove_NotP2(clau1,s1)
        if(Empty_clause(clau1)==True):
            return False
        if(DPLL(clau1,sym1,model1)==True):
            return True
        else:
            model2.append([s2,False])
            clau2=Remove_Notclauses(clauses,s2)
            clau2=Remove_P2(clau2,s2)
            if(Empty_clause(clau2)==True):
                return False
            return DPLL(clau2,sym2,model2)
        ########################## Splitting rule ###############################
        return False
    return False

# checks and corrects if a clause is of the form ["and", "A", []] => "A"
def Check_all(clauses):
    if(isinstance(clauses,list) and len(clauses)!=0 and clauses[0]=='and'):
        str=["and"]
        for x in range(1,len(clauses)):
            if(Check_single(clauses[x])[0]==True):
                str=str+[Check_single(clauses[x])[1]]
            else:
                str=str+[clauses[x]]
        return str
    return clauses


# supporting fucntion for check_all
def Check_single(clauses):
    if isinstance(clauses,list) and len(clauses)!=0:
        q=0
        r=0
        if(clauses[0]=='or'):
            q=0
            r=0
            val=""
            for x in range(1,len(clauses )):
                if(not isinstance(clauses[x],list)):
                    val=clauses[x]
                    q=q+1
                if(isinstance(clauses[x],list) and len(clauses[x])==0):
                    r=r+1
            if(q==1 and r==len(clauses)-2):
                return [True, val]
            q=0
            r=0
            for x in range(1,len(clauses )):
                if( isinstance(clauses[x],list) and len(clauses[x])!=0):
                    if( clauses[x][0] =='not'):
                        val=clauses[x][1]
                        q=q+1
                if(isinstance(clauses[x],list) and len(clauses[x])==0):
                    r=r+1
            if(q==1 and r==len(clauses)-2):
                return [True, ["not", val]]

    return [False, ""]

# checks for empty clauses.
def Empty_clause(clauses):
    if(isinstance(clauses,list) and len(clauses)!=0 and clauses[0]=='and' ):
        for x in clauses:
                if isinstance(x,list) and len(x)==0:
                    return True
    return False

# supporting function for pure symbol rule. removes unnecessary clauses
def Remove_Notclauses(clauses,symbol):
    if isinstance(clauses,list) and len(clauses)!=0:
        if(clauses[0]=='and'):
            str=["and"]
            for cl in range(1,len(clauses)):
                if(Check_singel_notClause2([clauses[cl]],symbol)==True):
                    str=str+[]
                else:
                    str=str+[clauses[cl]]
            return str

# supporting function for pure symbol rule. removes unnecessary clauses
def Remove_clauses(clauses,symbol):
    if isinstance(clauses,list) and len(clauses)!=0:
        if(clauses[0]=='and'):
            str=["and"]
            for cl in range(1,len(clauses)):
                if(Check_singel_Clause2([clauses[cl]],symbol)==True):
                    str=str+[]
                else:
                    str=str+[clauses[cl]]
            return str

# supporting funciton for remove_notclause
def Check_singel_notClause2(clauses,symbol):
    for x in clauses:
        if isinstance(x,list) and len(x)!=0:
            if x[0]=='not' and x[1]==symbol:
                #print 5555, symbol
                return True
            if x[0]=='or':
                for i in range(1,len(x)):
                    if(Check_singel_notClause([x[i]],symbol)==True):
                        return True
    return False

# checks if it is sungel not clause
def Check_singel_notClause(clauses,symbol):
    for x in clauses:
        if isinstance(x,list) and len(x)!=0:
            if x[0]=='not' and x[1]==symbol:
                return True
    return False

# supporting funciton for remove_clause. for unit clause.
def Check_singel_Clause2(clauses,symbol):
    for x in clauses:
        if ((not isinstance(x,list)) and x==symbol):
            return True
        if isinstance(x,list) and len(x)!=0:
            if x[0]=='or':
                for i in range(1,len(x)):
                    if(Check_singel_Clause([x[i]],symbol)==True):
                        return True
    return False

# check if the input id a single clause. for unit clause.
def Check_singel_Clause(clauses,symbol):
    for x in clauses:
        if ((not isinstance(x,list)) and x==symbol):
            return True
    return False


# supporting function for pure symbol and unit clause rule. removes unnecessary symbols from clauses
def Remove_P2(clauses,symbol):
    if not isinstance(clauses,list):
        if(symbol==clauses):
            return []
        else:
            return clauses
    if (len(clauses)==0):
        return []
    elif(clauses[0]=='not'):
        return clauses
    elif(clauses[0]=='and'):
        lst=["and"]
        for x in range(1,len(clauses)):
            lst=lst+[Remove_P2(clauses[x],symbol)]
        return lst
    elif(clauses[0]=='or'):
        lst=["or"]
        for x in range(1,len(clauses)):
            lst=lst+[Remove_P2(clauses[x],symbol)]
        return lst
    else:
        return []

# supporting function for pure symbol and unit clause rule. removes unnecessary symbols from clauses
def Remove_NotP2(clauses,symbol):
    if not isinstance(clauses,list):
        return clauses
    if (len(clauses)==0):
        return []
    elif(clauses[0]=='not'):
        if(clauses[1]==symbol):
            return []
        else:
            return clauses
    elif(clauses[0]=='and'):
        lst=["and"]
        for x in range(1,len(clauses)):
            lst=lst+[Remove_NotP2(clauses[x],symbol)]
        return lst
    elif(clauses[0]=='or'):
        lst=["or"]
        for x in range(1,len(clauses)):
            lst=lst+[Remove_NotP2(clauses[x],symbol)]
        return lst
    else:
        return []


# checks for single occurances of clauses. for pure symbol.
def Check_occurances_single(clauses,symbol):
    if not isinstance(clauses,list):
        if clauses==symbol:
            return True
        else:
            return False
    if (len(clauses)==0):
        return True
    elif(clauses[0]=='not'):
        return False
    elif(clauses[0]=='and'):
        for x in range(1,len(clauses)):
            if(Check_occurances_single(clauses[x],symbol)==True):
                return True
        return False
    elif(clauses[0]=='or'):
        for x in range(1,len(clauses)):
            if(Check_occurances_single(clauses[x],symbol)==True):
                return True
        return False
    return False

# checks for single occurances of not clauses. for pure symbol.
def Check_occurances_notSingle(clauses,symbol):
    if not isinstance(clauses,list):
        return False
    if (len(clauses)==0):
        return False
    elif(clauses[0]=='not'):
        if clauses[1]==symbol:
            return True
        else:
            return False
    elif(clauses[0]=='and'):
        for x in range(1,len(clauses)):
            if(Check_occurances_notSingle(clauses[x],symbol)==True):
                return True
        return False
    elif(clauses[0]=='or'):
        for x in range(1,len(clauses)):
            if(Check_occurances_notSingle(clauses[x],symbol)==True):
                return True
        return False
    return False

# checks for the correct argument. opens the file. calls DPLL
if(sys.argv[1]=='-i'):
    with open(sys.argv[2], "r") as ins:
        array = []
        for line in ins:
            array.append(eval(line.rstrip('\n').rstrip('\r')))
    num=array[0]
    lst=array[1:num+1]
    f = open('CNF_satisfiability.txt', 'w')
    g=0 
    mod=[]
    for line in lst:
        printable=[]
        d=Make_Symbol(line)
        set_list=set(d)
        final_lst=list(set_list)
        mod=[]
        val= DPLL(line,final_lst,[])
        if(val==True):
            printable=["true"]
            for [x,y] in mod:
                printable=printable+[str(x)+"="+str(y).lower()]
            f.write(str(printable)+"\n")
        else:
            printable=["false"]
            f.write(str(printable)+"\n")    
        g=g+1
