"""
This CNF converter converts propostion logic statemets to clauses.
"""

import sys

# This Equal function removes the diff operator.
def Equal(prop):
    if prop[0]=='iff':
        return ["and",["implies", Equal(prop[1]),Equal(prop[2])],["implies",Equal(prop[2]),Equal(prop[1])]]
    elif prop[0]=='and':
        return ['and', Equal(prop[1]),Equal(prop[2])]
    elif prop[0]=='or':
        return ['or', Equal(prop[1]),Equal(prop[2])]
    elif prop[0]=='not':
        return ["not", Equal(prop[1])]
    else:
        return prop

# This Implies function removes the implies operator.
def Implies(prop):
    if prop[0]=='implies':
        return ["or", ["not", Implies(prop[1])], Implies(prop[2])]
    elif prop[0]=='and':
        return ["and", Implies(prop[1]), Implies(prop[2])]
    elif prop[0]=='or':
        return ["or", Implies(prop[1]), Implies(prop[2])]
    elif prop[0]=='not':
        return ["not", Implies(prop[1])]
    else:
        return prop

# This DeM fuction pushes nots downwards -- Demorgan law
def DeM(prop):
    if prop[0]=='not':
        if not isinstance(prop[1],list):
            return prop
        elif prop[1][0]=='and':
            return ["or", DeM(["not", prop[1][1]]), DeM(["not", prop[1][2]])]
        elif prop[1][0]=='or':
            return ["and", DeM(["not", prop[1][1]]), DeM(["not", prop[1][2]])]
        elif prop[1][0]=='not':
            return DeM(prop[1][1])
    elif prop[0]=='and':
        return ["and", DeM(prop[1]), DeM(prop[2])]
    elif prop[0]=='or':
        return ["or", DeM(prop[1]), DeM(prop[2])]    
    else:
        return prop

# uses the distributive property to push \/ over /\ -- pushes disjuctions downwards
def Dis(prop):
    if prop[0]=='or':
        if isinstance(prop[2],list) and prop[2][0]=='and':
            return ["and", Dis(["or", prop[1], prop[2][1]]),Dis(["or", prop[1], prop[2][2]])]
        elif isinstance(prop[1],list) and prop[1][0]=='and':
            return ["and", Dis(["or", prop[1][1], prop[2]]),Dis(["or", prop[1][2], prop[2]])]
        else:
            return ["or", Dis(prop[1]), Dis(prop[2])]
    elif prop[0]=='and':
        return ["and", Dis(prop[1]), Dis(prop[2])]
    elif prop[0]=='not':
        return ["not", Dis(prop[1])]
    else:
        return prop

# removes unnecessary or's. ie removes the brackets using the associative rule.
def Asso(prop):
    if prop[0]=='and':
        x=len(prop)
        i=1
        f=False
        while(i<x):
            if(isinstance(prop[i],list) and prop[i][0]=='and'):
                prop=["and"]+prop[1:i]+Rtn_list(prop[i][1])+Rtn_list(prop[i][2])+prop[i+1:]
                f=True
                x=x+1
            if(f==False):
                i=i+1
            else:
                i=1
                f=False
    if prop[0]=='and':
        prop=prop[1:]
        final=[]
        for propp in prop:
            if propp[0]=='or':
                x=len(propp)
                i=1
                f=False
                while(i<x):
                    if(isinstance(propp[i],list) and propp[i][0]=='or'):
                        propp=["or"]+propp[1:i]+Rtn_list(propp[i][1])+Rtn_list(propp[i][2])+propp[i+1:]
                        f=True
                        x=x+1
                    if(f==False):
                        i=i+1
                    else:
                        i=1
                        f=False
            final=final+[propp]
        prop=["and"]+final

    if prop[0]=='or':
        x=len(prop)
        i=1
        f=False
        while(i<x):
            if(isinstance(prop[i],list) and prop[i][0]=='or'):
                prop=["or"]+prop[1:i]+Rtn_list(prop[i][1])+Rtn_list(prop[i][2])+prop[i+1:]
                f=True
                x=x+1
            if(f==False):
                i=i+1
            else:
                i=1
                f=False
    return prop

# removes any duplicate occurances of literals. 
def RemoveDup(prop):
    if(not isinstance(prop,list)):
        return prop
    elif(prop[0]=='not'):
        return ["not", RemoveDup(prop[1])]
    else:
        # remove duplicates and make a list; call it dub
        dub=[]
        depth=len(prop)
        i=1;
        while(i<depth):
            j=i+1
            while(j<depth):
                if(str(prop[i])==str(prop[j])):
                    #print "before pop\n"
                    #print prop
                    prop.pop(j)
                    #print "after pop\n"
                    #print prop
                    depth=depth-1
                j=j+1
            dub=dub+[prop[i]]
            i=i+1
        #print "dubb", dub
        # remove duplicates and make a list; call it dub
        lst=[]
        for ele in dub:
            if(isinstance(ele,list)):
                x=RemoveDup(ele)
            else:
                x=ele
            lst=lst+[x]
        return [prop[0]]+lst

# evaluates redundant euqations. like ["and","A"] => "A". This function is to be called after duplicate literals are removed.
def Singlele(prop):
    if(not isinstance(prop,list)):
        return prop
    elif(prop[0]=='not'):
        return ["not", Singlele(prop[1])]
    elif (prop[0]=='and' and len(prop)==2):
        return Singlele(prop[1])
    elif (prop[0]=='and' and len(prop)>2):
        lst=[]
        for i in range(1,len(prop)):
            lst=lst+[Singlele(prop[i])]
        return ["and"]+lst
    elif (prop[0]=='or' and len(prop)==2):
        return Singlele(prop[1])
    elif (prop[0]=='or' and len(prop)>2):
        lst=[]
        for i in range(1,len(prop)):
            lst=lst+[Singlele(prop[i])]
        return ["or"]+lst


def Rtn_list(var):
    if(isinstance(var,list)):
        return [var]
    else:
        return [var]

# The CNF fuctions which converts a proposition logic string to its CNF form and returns it
def CNF(prop):
    if prop[0].isupper():
        return prop
    prop= Equal(prop)
    prop= Implies(prop)
    prop= DeM(prop)
    prop1=list(Dis(prop))
    prop2= list(Dis(prop1))
    if(prop2!=prop1):
        prop1=list(Dis(prop2))
        prop2= list(Dis(prop1))
    prop= Asso(prop2)
    prop= RemoveDup(prop)
    prop= Singlele(prop)
    return prop

if(sys.argv[1]=='-i'):
    with open(sys.argv[2], "r") as ins:
        array = []
        for line in ins:
            array.append(eval(line.rstrip('\n').rstrip('\r')))

    num=array[0]
    lst=array[1:num+1]
    f = open('sentences_CNF.txt', 'w')
    g=0
    for line in lst:
        flag=False
        d=CNF(line)
        if(not isinstance(d,list)):
            flag=True
        strr=str(d)
        if(g!=num-1):
            strr+="\n"
        if(flag==True):
            f.write("\""+d+"\"")
            if(g!=num-1):
                f.write("\n")
        else:
            f.write(strr)
        g=g+1