'''
EDA project :: Implementing a Netlist Equivalence checker using SAT approach.
Sumbitted by: Muahmmad Ali Danish. Matrcl #332211. email: alidanish@outlook.de
@author: Ali Danish
year 2014
'''

import sys
from collections import deque
import pdb
import copy

def readNetlist(file):

    nets = int(file.readline())
    inputs  = file.readline().split()
    inputs.sort()
    outputs = file.readline().split()
    outputs.sort()

    # read mapping
    mapping = {} #following the net file pattern
    while True:
        #at this time line read will be after 3rd line
        line = file.readline().strip()
        if not line:
            break

        net,name = line.split()
        mapping[name] = int(net)

    # read gates
    gates = []

    for line in file.readlines():
        gp = {}
        bits = line.split() #forming the line/listing in list type data structure from the gate and its corresponding ports
        print(bits)
        gate = bits.pop(0)  #being list formed poping the zeroth item which is the name of the gate
        ports = map(int,bits) #applying int to net number which were strings thus converting them into integer
        gp[gate] = ports
        gates.append(gp)
    return inputs,outputs,mapping,gates, nets

# read netlists

def litrcrtn():
    inputs1,outputs1,mapping1,gates1,nets1= readNetlist(open(sys.argv[1],"r")) #reading netlist from the funciton and separating the data struct at the same time
    inputs2,outputs2,mapping2,gates2,nets2= readNetlist(open(sys.argv[2],"r"))
    print("From netlist1::",inputs1, outputs1, mapping1, gates1,nets1)
    print("From netlist2::",inputs2, outputs2, mapping2, gates2,nets2)
    key = ''
    vlist = []
    gatelist1 = []
    gatelist2 = []
    gatedict1 = {}
    gatedict2 = {}


    kvpr = dict() #for renaming 2nd netlist literals, the renaming range can be extended as problem requires it to be.

    startrn = 101 #2nd netlist renaming starts from here.
    rn = nets2
    litmar1 = 1
    endrn = startrn + rn + litmar1
    keyst = 1
    keyend = rn + litmar1

    if (len(outputs2) == 1):
        valpr = range(startrn, endrn)
        # print(valpr)
        keypr = range(keyst, keyend)
        # print(keypr)
        kvpr = dict(zip(keypr, valpr))
        # print(kvpr)
    elif(len(outputs2)>1):
        litmar2 = 8
        endrn = startrn + rn + litmar2
        keyend = rn + litmar2
        valpr = range(startrn, endrn)
        keypr = range(keyst, keyend)
        kvpr = dict(zip(keypr, valpr))

    for x in gates1:
        for k, v in x.items():
            ky = k
            vl = list(v)
            # print('1st netlist lit',ky, vl)
            gatedict1 = gateslsfm(ky, vl)
            gatelist1.append(gatedict1)

    for g in gates2:
        for k, v in g.items():
            key = k
            vlist = list(v)
            for ky,vl in kvpr.items():
                if ky in vlist:
                    ind = vlist.index(ky)
                    vlist.remove(ky)
                    vlist.insert(ind, vl)
            # print('2nd netlist lit',key, vlist)
            gatedict2 = gateslsfm(key, vlist)
            gatelist2.append(gatedict2)

    #the working code area for more than 1 o/p
    print('this is gatelist1::', gatelist1)
    print('this is gatelist2::', gatelist2)

    if(len(outputs2) > 1):
        print('tracking more than 1 o/p.....')
        moreop(kvpr, outputs2, mapping2) #mapping2 would be changed
    else:
        if 'f_0' in mapping2:
            fkey = mapping2.get('f_0', 'none')
            if fkey in kvpr:
                fkvpr = kvpr.get(fkey, 'none') #getting the renamed value
                mapping2['f_0'] = [fkey, fkvpr] #o/p var is tracked for miter buildup


    srchlst = []
    lstkeys = kvpr.keys()
    lstvalues = kvpr.values()
    srchlst.extend(lstkeys)
    srchlst.extend(lstvalues)
    revlist = list(reversed(sorted(srchlst)))#for elements to iter the solvestack in solvecnf

    miterdic = mitrcir(kvpr,mapping1,mapping2,outputs1,outputs2)
    for l in miterdic:
        gatelist2.append(l) #miter is added to gatelist2 bcz in the end every list is added in the all gate stack

    print('this is gatelist2',gatelist2)
    equivdic = equivfunc(inputs1, inputs2, mapping1, mapping2, kvpr)
    gatelist2.append(equivdic)
#   print('2nd gatelist incl. miter&equiv:', gatelist2)
    allgatestack = gatesstack(gatelist1, gatelist2)
    solvestack = cnf(allgatestack, inputs1)
    # print("this is complete stack that will be solved:::::",solvestack)
    reclst = []
    solvecnf(solvestack,revlist, reclst,inputs1,inputs2,outputs1,outputs2,mapping1,mapping2,kvpr)

def moreop(kvpr,outputs2,mapping2): #o/p tracking for renamed o/ps in mapping2

    for x in outputs2:
        if x in mapping2:
            opval = mapping2.get(x,'none')
            if opval in kvpr:
                vkvpr = kvpr.get(opval, 'none')
                mapping2[x] = [opval, vkvpr]
    print('tracked mapping2::', mapping2)

def solvecnf(solvestack,revlist, reclst,inputs1,inputs2,outputs1,outputs2,mapping1,mapping2,kvpr):
#    pdb.set_trace()
#    print ("entering solvecnf")


    for y in solvestack[:]:
        if( len(y) == 1):
            if (y[0] < 0):
                print(y[0])
                print('start')
                pfm = '{0}'.format(y[0]) #opposite form making for pop
                pive = -int(pfm) #- and - is plus...oops
                for j in solvestack[:]:
                    if (y[0] in j):
                        rec = {}
                        rec[y[0]] = 0
                        reclst.append(rec)
                        solvestack.remove(j)

                        for k in solvestack:
                            if(pive in k):
                                ix = k.index(pive)
                                k.pop(ix)
                                rec[y[0]] = 1
                                reclst.append(rec)


            elif (y[0]>0):
                print(y[0])
                rec = {}
                pfm = '-{0}'.format(y[0])
                nive = int(pfm)
                for u in solvestack[:]:
                    if (y[0] in u):
                        rec[y[0]] = 1
                        reclst.append(rec)
                        solvestack.remove(u)

                        for i in solvestack:
                            if(nive in i):
                                ind = i.index(nive)
                                i.pop(ind)
                                rec[y[0]] = 0
                                reclst.append(rec)

    # print(solvestack)

    if (len(solvestack) == 0):
        print('SOLUTION FOUND, NOT EQUIVALENT! COUNTER EXAMPLE:::::::::::::::\n')
        print("The whole solution stack recorded as ::::::::::::::::::::::::::::::::\n", reclst)
        print(":::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::\n")
        opint(reclst, inputs1, inputs2, outputs1, outputs2, mapping1, mapping2, kvpr)
        sys.exit()

    elif (len(solvestack) == 1):
        if (len(solvestack[0]) == 0):
            print('NO SOLUTION, EQUIVALENT!')
            print("The whole solution stack recorded as ::::::::::::::::::::::::::::::::\n", reclst)
            print(":::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::\n")
            opint(reclst, inputs1, inputs2, outputs1, outputs2, mapping1, mapping2, kvpr)
            sys.exit()


    e = solvestack[-1][-1] #used to access the last element in the list
    ed = -e
    solvecnfone = copy.deepcopy(solveone(solvestack, e, ed, reclst))
    solvecnf(solvecnfone,revlist, reclst,inputs1,inputs2,outputs1,outputs2,mapping1,mapping2,kvpr)
    solvecnfzero = copy.deepcopy(solvezero(solvestack, e, ed, reclst))
    solvecnf(solvecnfzero, revlist, reclst,inputs1,inputs2,outputs1,outputs2,mapping1,mapping2,kvpr)
    return

def opint(reclst,inputs1,inputs2,outputs1,outputs2,mapping1,mapping2,kvpr):

    qstack = deque([])
    fdlst = []
    for n in inputs2:
        if n in mapping2: #i/ps in mapping
            ipval = mapping2.get(n, 'none')
            if (ipval in kvpr):
                valkvpr = kvpr.get(ipval,'none')
                mapping2[n] = [ipval, valkvpr]
    # print('mapping with renamed ip and op::',mapping2)
    for x in inputs2:
        if x in mapping2:
            glst = mapping2.get(x,'none')
            fdlst.append(glst[-1])
    for o in outputs2: #stacking ops in fdlst to search in the reclst
        if o in mapping2:
            glst = mapping2.get(o,'none')
            fdlst.append(glst[-1])

    for i in inputs1: #  stacking ips of netlist1 in fdlst
        if i in mapping1:
            ival = mapping1.get(i, 'none')
            fdlst.append(ival)
    for k in outputs1:
        if k in mapping1:
            kval = mapping1.get(k, 'none')
            fdlst.append(kval)

    invlst = [-x for x in fdlst]# convert the list in oppposite form to search.
    fdlst.extend(invlst)
    print(invlst)

    print(fdlst)
    for renlit in fdlst:
        for d in reclst:
            for k,v in d.items():
                if(renlit == k) and (d not in qstack):
                    qstack.append(d)
                    print(qstack)

    soldic = dict()
    dic = dict()
    idic = dict()
    while (len(qstack)>0):
        dic = qstack.pop()
        for k,v in dic.items():
            if(k not in soldic) and (len(dic)<2):
                print(len(dic))
                soldic.update(dic)
            elif(k not in soldic) and (len(dic)>=2):
                for j,l in dic.items():
                    if(j>0):
                        idic[j] = l
                        soldic.update(idic)

        print(soldic)
    insd = dict()
    for g,h in soldic.items():
        if (g < 0):
            gop = -int(g)
            # print(gop)
            insv = soldic.pop(g) #remove the key and return its value.
            insd[gop] = insv
            soldic.update(insd)
    print('to be searched in the mappings soldic::',soldic)

    fdc1 = dict()   #populating fdc according elements found in mapping1
    for kym,vlm in mapping1.items():
        for kys, vls in soldic.items():
            if(vlm == kys):
                fdc1 [kym] = {kys:vls}
    # print(fdc1)

    for ip1 in inputs1:
        if (ip1 in fdc1):
            ip1v = fdc1.get(ip1)
            print("inputs from netlist1::", {ip1:ip1v})
    for op1 in outputs1:
        if(op1 in fdc1):
            op1v = fdc1.get(op1)
            print("outputs form netlist1::", {op1:op1v})

    # print(mapping2, inputs2)

    fdc2 = dict()
    for keym, valm in mapping2.items():
        for keys, vals in soldic.items():
            if(valm[-1] == keys):
                fdc2 [keym] = {keys:vals}
    # print(fdc2)

    for ip2 in inputs2:
        if (ip2 in fdc2):
            ip2vl = fdc2.get(ip2)
            print("inputs from netlist2::", {ip2:ip2vl})

    for op2 in outputs2:
        if(op2 in fdc2):
            op2vl = fdc2.get(op2)
            print("outputs from netlist2::", {op2:op2vl})


def solveone(solvestack, e, ed, reclst):
    print('one kick in, e: %d ed: %d' % ( e, ed))
    rec = {}
    for ls in solvestack[:]:
        if (e in ls):
            solvestack.remove(ls)
            rec[e] = 1
            reclst.append(rec)
    for opls in solvestack:
        if ed in opls:
            ckind = opls.index(ed)
            opls.pop(ckind)
            rec[ed] = 0
            reclst.append(rec)
    print(solvestack)
    return solvestack

def solvezero(solvestack, e, ed, reclst):
    print('zero kick in, e: %d, ed: %d' % (e,ed))
    rec = {}
    for ls in solvestack[:]:
        if ed in ls:
            rec[ed] = 0
            reclst.append(rec)
            solvestack.remove(ls)
    for opls in solvestack:
        if e in opls:
            ind = opls.index(e)
            opls.pop(ind)
            rec[e] = 1
            reclst.append(rec)
    print(solvestack)
    return solvestack


def gateslsfm(key,flist):


    gatedict = {}

    gatedict[key] = flist

    # print('gates in list wil be',gatedict)
    return gatedict;

def mitrcir(kvpr,mapping1,mapping2,outputs1,outputs2):
    lstfcnt = []
    addgate ={}
    orsin = {}
    orsinlst = []

    # addgatelst = [] #making mitercir in case of 5xor

    if (len(outputs1) > 1):
        addgatelst = xor5lit(mapping1, mapping2, kvpr, outputs1, outputs2)
    else:

        print('this is mapping 1',mapping1, 'this is mapping 2', mapping2)
        if ('f_0' in mapping1 and mapping2):
            fmpkey1 = mapping1.get('f_0','none')
            fmpkey2 = mapping2.get('f_0','none')
            kcnt0 = fmpkey2[1]+1 #xor o/p
            kcnt1 = fmpkey2[1]
            lstfcnt.append(fmpkey1)
            lstfcnt.append(kcnt1)
            lstfcnt.append(kcnt0)
            addgate['xor'] = lstfcnt
            orsinlst.append(kcnt0)
            orsin['orsin'] = orsinlst

            print('xor for mitercir::',addgate, orsin)
        return [addgate, orsin]
    return addgatelst

def xor5lit(mapping1, mapping2, kvpr, outputs1, outputs2): #extends mitercir
    addgatelst = []
    valuslst = []
    xorop6 = []
    xrq = deque([]) #a queue list to put all elements

    qlit1 = deque([]) #implement queue for making alias based correspondence btw lits that were extracted from the mapping
    qlit2 = deque([])

    for x in outputs2:
        if x in mapping2:
            fvalu = mapping2.get(x,'none')
            fvalulst = fvalu[1]
            valuslst.append(fvalulst)

    valmax = max(valuslst)
    print("so the max in the list is::",valmax)

        # after establishing a max value we need more literal for xor and or in mitercir
    cxr1 = valmax+1 #getting count ahead from the max value that was determined to get lit from kvpr
    xorop6.append(cxr1)
    cxr2 = cxr1+1
    xorop6.append(cxr2)
    cxr3 = cxr2+1
    xorop6.append(cxr3)
    cxr4 = cxr3+1
    xorop6.append(cxr4)
    cxr5 = cxr4+1
    xorop6.append(cxr5)
    cxr6 = cxr5+1
    xorop6.append(cxr6)
    print('gates from the lit margin',xorop6)
    print('list for output1:::::',outputs1, '.......and its mapping1 is >>>', mapping1)
    print('list for output2:::::',outputs2, '.......and its mapping2 is >>>', mapping2)

    for z in outputs1:
        if z in mapping1:
            kg1 = mapping1.get(z,'none')
            qlit1.append(kg1)
            print('the q1 is ::', qlit1)

    for v in outputs2:
        if v in mapping2:
            kg2 = mapping2.get(v, 'none')
            kgf = kg2[1]
            qlit2.append(kgf)
            print('the q2 is ::',qlit2)

    i= 0 #used in appending margin lit with
    while(len(qlit1 and qlit2)>0): #in order to make individual xors, made a pattern of two i/p followed by o/p
        klit1 = qlit1.popleft()
        klit2 = qlit2.popleft()
        xrq.append(klit1)
        xrq.append(klit2)
        xrq.append(xorop6[i])
        i = i+1
    print('the final ip op is 5xor::', xrq)

    #now making xor gates with pattern supplied in the xrq queue

    addgate1 = {}
    addgate2 = {}
    addgate3 = {}
    addgate4 = {}
    addgate5 = {}

    xrg1 = []
    xrg2 = []
    xrg3 = []
    xrg4 = []
    xrg5 = []

    print(xrq)
    while (len(xrq)>0):
        xr1 = xrq.popleft()
        xr2 = xrq.popleft()
        xro = xrq.popleft()
        xrg1.append(xr1)
        xrg1.append(xr2)
        xrg1.append(xro)

        xr1 = xrq.popleft()
        xr2 = xrq.popleft()
        xro = xrq.popleft()
        xrg2.append(xr1)
        xrg2.append(xr2)
        xrg2.append(xro)

        xr1 = xrq.popleft()
        xr2 = xrq.popleft()
        xro = xrq.popleft()
        xrg3.append(xr1)
        xrg3.append(xr2)
        xrg3.append(xro)

        xr1 = xrq.popleft()
        xr2 = xrq.popleft()
        xro = xrq.popleft()
        xrg4.append(xr1)
        xrg4.append(xr2)
        xrg4.append(xro)

        xr1 = xrq.popleft()
        xr2 = xrq.popleft()
        xro = xrq.popleft()
        xrg5.append(xr1)
        xrg5.append(xr2)
        xrg5.append(xro)

        addgate1['xor']=xrg1
        addgatelst.append(addgate1)
        addgate2['xor']=xrg2
        addgatelst.append(addgate2)
        addgate3['xor'] = xrg3
        addgatelst.append(addgate3)
        addgate4['xor'] = xrg4
        addgatelst.append(addgate4)
        addgate5['xor'] = xrg5
        addgatelst.append(addgate5)


    addgate6={}

    addgate6['opmitr'] = xorop6 #this is the final gate having 5inputs from xor gates and the last element is the op of OR gate
    addgatelst.append(addgate6)

    print('5op xor gate mitercir:::',addgatelst)
    return addgatelst


def equivfunc(inputs1, inputs2, mapping1, mapping2, kvpr):#equiv gate is formed here
    #after comparing mapping2 of inputs2 and equiv gate function it seems that equiv func requires no change.
    equivls = []
    equivg = {}

    for x in inputs1:
        if x in mapping1:
            fky = mapping1.get(x,'none')
            equivls.append(fky)

    for y in inputs2:
        if y in mapping2:
            fky = mapping2.get(y,'none')
            if fky in kvpr:
                nky = kvpr.get(fky,'none')
            equivls.append(nky)
    equivg['equiv'] = equivls
    return(equivg)

def gatesstack(gatelist1, gatelist2):
    appgatelst = []
    for x in gatelist1:
        appgatelst.append(x)

    for y in gatelist2:
        appgatelst.append(y)

    return appgatelst

def cnf(allgatestack, inputs1):
    print("cnf will be form from this stack::", allgatestack)
    solvelst = []
    convlst = []
    for x in allgatestack:
        if 'xor' in x:
            #print('found xor')
            fnky = x.get('xor','none')
            in1 = fnky[0]
            in2 = fnky[1]
            op = fnky[2]
            xr1 = "{0},{1},-{2}".format(in1,in2,op)
            xrg = xr1.split(",")
            solvelst.append(xrg)
            xr2 = "{0},-{1},{2}".format(in1,in2,op)
            xrg = xr2.split(",")
            solvelst.append(xrg)
            xr3 = "-{0},{1},{2}".format(in1,in2,op)
            xrg = xr3.split(",")
            solvelst.append(xrg)
            xr4 = "-{0},-{1},-{2}".format(in1,in2,op)
            xrg = xr4.split(",")
            solvelst.append(xrg)

        elif 'and' in x:
            finkey = x.get('and','none')
            in1 = finkey[0]
            in2 = finkey[1]
            op = finkey[2]
#            print('and gate found')
            and1 = "{0},-{2}".format(in1,in2,op)
            andg = and1.split(",")
            solvelst.append(andg)
            and2 = "{1},-{2}".format(in1,in2,op)
            andg = and2.split(",")
            solvelst.append(andg)
            and3 = "-{0},-{1},{2}".format(in1,in2,op)
            andg = and3.split(",")
            solvelst.append(andg)

        elif 'inv' in x:
            finkey = x.get('inv','none')
            in1 = finkey[0] #in case of an inv this is ip
            in2 = finkey[1] #in case of an inv this is op
#            print('inv gate found')
            inv1 = "{0},{1}".format(in1,in2) #in case of inv in2 is op
            invg = inv1.split(",")
            solvelst.append(invg)
            inv2 = "-{0},-{1}".format(in1,in2) #in case of inv in2 is op
            invg = inv2.split(",")
            solvelst.append(invg)

        elif 'or' in x:
            finkey = x.get('or','none')
            in1 = finkey[0]
            in2 = finkey[1]
            op = finkey[2]
#            print('or gate found')
            or1 = "-{0},{2}".format(in1,in2,op)
            org = or1.split(",")
            solvelst.append(org)
            or2 = "-{1},{2}".format(in1,in2,op)
            org = or2.split(",")
            solvelst.append(org)
            or3 = "{0},{1},-{2}".format(in1,in2,op)
            org = or3.split(",")
            solvelst.append(org)

        elif (len(inputs1)>2):
            if 'equiv' in x:

                finkey = x.get('equiv', 'none')
                in0 = finkey[0]
                in1 = finkey[1]
                in2 = finkey[2]
                in3 = finkey[3]
                in4 = finkey[4]
                in5 = finkey[5]
                in6 = finkey[6]
                in7 = finkey[7]
                in8 = finkey[8]
                in9 = finkey[9]
                in10 = finkey[10]
                in11 = finkey[11]
                in12 = finkey[12]
                in13 = finkey[13]
                in14 = finkey[14]
                in15 = finkey[15]
                in16 = finkey[16]
                in17 = finkey[17]
#                print('equiv gate found 5op')
                equiv1 = "{0},-{9}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv1.split(",")
                solvelst.append(equivg)
                equiv2 = "-{0},{9}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv2.split(",")
                solvelst.append(equivg)
                equiv3 = "{1},-{10}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv3.split(",")
                solvelst.append(equivg)
                equiv4 = "-{1},{10}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv4.split(",")
                solvelst.append(equivg)
                equiv5 = "-{11},{2}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv5.split(",")
                solvelst.append(equivg)
                equiv6 = "{11},-{2}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv6.split(",")
                solvelst.append(equivg)
                equiv7 = "-{12},{3}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv7.split(",")
                solvelst.append(equivg)
                equiv8 = "{12},-{3}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv8.split(",")
                solvelst.append(equivg)
                equiv9 = "-{13},{4}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv9.split(",")
                solvelst.append(equivg)
                equiv10 = "{13},-{4}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv10.split(",")
                solvelst.append(equivg)
                equiv11 = "-{14},{5}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv11.split(",")
                solvelst.append(equivg)
                equiv12 = "{14},-{5}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv12.split(",")
                solvelst.append(equivg)
                equiv13 = "-{15},{6}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv13.split(",")
                solvelst.append(equivg)
                equiv14 = "{15},-{6}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv14.split(",")
                solvelst.append(equivg)
                equiv15 = "-{16},{7}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv15.split(",")
                solvelst.append(equivg)
                equiv16 = "{16},-{7}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv16.split(",")
                solvelst.append(equivg)
                equiv17 = "-{17},{8}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv17.split(",")
                solvelst.append(equivg)
                equiv18 = "{17},-{8}".format(in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,in10,in11,in12,in13,in14,in15,in16,in17)
                equivg = equiv18.split(",")
                solvelst.append(equivg)

            elif 'opmitr' in x:
                finkey = x.get('opmitr', 'none')
                in0 = finkey[0]
                in1 = finkey[1]
                in2 = finkey[2]
                in3 = finkey[3]
                in4 = finkey[4]
                in5 = finkey[5]
#                print('opmitr gate found')
#                opmitrg = "-{0},{5},-{1},{5},-{2},{5},-{3},{5},-{4},{5},{0},{1},{2},{3},{4},-{5}".format(in0,in1,in2,in3,in4,in5)

#                opmitr1 = "-{0},{5}".format(in0,in1,in2,in3,in4,in5)
#                opmitrg = opmitr1.split(",")
#                solvelst.append(opmitrg)
#                opmitr2 = "-{1},{5}".format(in0,in1,in2,in3,in4,in5)
#                opmitrg = opmitr2.split(",")
#                solvelst.append(opmitrg)
#                opmitr3 = "-{2},{5}".format(in0,in1,in2,in3,in4,in5)
#                opmitrg = opmitr3.split(",")
#                solvelst.append(opmitrg)
#                opmitr4 = "-{3},{5}".format(in0,in1,in2,in3,in4,in5)
#                opmitrg = opmitr4.split(",")
#                solvelst.append(opmitrg)
#                opmitr5 = "-{4},{5}".format(in0,in1,in2,in3,in4,in5)
#                opmitrg = opmitr5.split(",")
#                solvelst.append(opmitrg)
#                opmitr6 = "{0},{1},{2},{3},{4},-{5}".format(in0,in1,in2,in3,in4,in5)
#                opmitrg = opmitr6.split(",")
#                solvelst.append(opmitrg)
#                opmitr7 = "{5}".format(in0,in1,in2,in3,in4,in5)
#                opmitrg = opmitr7.split(",")
#                solvelst.append(opmitrg) #the o/p of the orgte to be put as 1

                opmitr6 = "{0},{1},{2},{3},{4}".format(in0, in1, in2, in3, in4)
                opmitrg = opmitr6.split(",")
                solvelst.append(opmitrg)

        elif(len(inputs1) == 2):
            if 'equiv' in x:
                finkey = x.get('equiv','none')
                in1 = finkey[0] #apply alternate algo here for generic input increase
                in2 = finkey[1]
                in3 = finkey[2]
                in4 = finkey[3]
#                print('equiv gate found')
                equiv1 = "{0},-{2}".format(in1,in2,in3,in4)#{0}==in1 {1}==in2 and so on
                equivg = equiv1.split(",")
                solvelst.append(equivg)
                equiv2 = "-{0},{2}".format(in1,in2,in3,in4)#{0}==in1 {1}==in2 and so on
                equivg = equiv2.split(",")
                solvelst.append(equivg)
                equiv3 = "{1},-{3}".format(in1,in2,in3,in4)#{0}==in1 {1}==in2 and so on
                equivg = equiv3.split(",")
                solvelst.append(equivg)
                equiv4 = "-{1},{3}".format(in1,in2,in3,in4)#{0}==in1 {1}==in2 and so on
                equivg = equiv4.split(",")
                solvelst.append(equivg)
            elif 'orsin' in x:
                finkey = x.get('orsin','none')
                solvelst.append(finkey)

    for y in solvelst:
        tmplst = list(map(int, y))
        convlst.append(tmplst)

    print('cnf ready to sovle', convlst)
    return convlst

if __name__ == '__main__':
    litrcrtn()
