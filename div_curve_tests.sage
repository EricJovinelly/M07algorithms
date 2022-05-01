#process_div_curve main program, set for characteristic 0.
#This is written for Sage 9.1
from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence
import sage.libs.singular.function_factory
from itertools import chain,product,combinations,permutations#,izip
groebner1 = sage.libs.singular.function_factory.ff.groebner
intersect1= sage.libs.singular.function_factory.ff.intersect
import time
import random
start_time=time.time()

#Should also import other groebner basis computations, specifically the one that computes a groebner basis from an existing groebner basis and an extra element.  This could save time in a lot of places where I compute groebner bases
interred1=sage.libs.singular.function_factory.ff.interred
facstd1=sage.libs.singular.function_factory.ff.facstd
factorize1=sage.libs.singular.function_factory.ff.factorize


#BEGIN: SYMMETRY SECTION

def convert_to_vect(str1):
    global timedict
    start=time.time()
    veclist=list(int(float(elt)) for elt in str1.split())
    if len(veclist) != 42:
        print("Error with converting string to vector")
    timedict['convert_to_vect']=timedict.get('convert_to_vect',0)+time.time()-start
    return vector(veclist)

order=dict()

order['div']=list(('d','5','345','45','245','145','045','35','235','135','035','25','125','025','15','015','05','4','34','234','134','034','24','124','024','14','014','04','3','23','123','023','13','013','03','2','12','012','02','1','01','0'))
order['curve']=list(('d','curve','345','245','145','045','235','135','035','125','025','015','45','35','25','15','05','234','134','034','124','024','014','123','023','013','012','34','24','14','04','23','13','03','12','02','01','4','3','2','1','0'))

def find_S7_rep(vect1,obj):  #placeholder, will implement after testing
    global timedict
    start=time.time()
    #return vect1
    #the goal is to find the string representative of str1 which is minimum among the orbit of str1 with respect to the order given by order
    #str1 is a string representing a divisor
    #order is a list of 42 objective functions, as well as their S7 stabilizers.  These are all Sn x Sm <= S7.
    
    #first, we convert str1 to a more usable format:
    #div=convert_to_frz(convert_to_vect(str1))
    div=convert_to_frz(vect1,obj)
    
    #then, we find the representative of div:
    min_div,acted_on_curve=find_S7_repre(div,order,obj)
    
    
    #then, we convert min_div back to a string:
    str2=convert_to_str(min_div,obj)
    #print convert_to_vect(str2)
    #print min_div
    #then, we print str2
    print(str2)
    timedict['symmetry']=timedict.get('symmetry',0)+time.time()-start
    return convert_to_vect(str2),acted_on_curve    

def convert_to_frz(vect2,obj):  #needs editing!!!!
    global timedict
    start=time.time()
    counter=0
    div=dict()
    div['d']=vect2[counter]
    counter+=1
    if obj=='curve':
        sgn=1
    elif obj=='div':
        sgn=-1
    for i in range(0,6):
        div[str(i)]=sgn*vect2[counter]
        counter+=1
    for i in range(0,6):
        for j in range(i+1,6):
            div[str(i)+str(j)]=sgn*vect2[counter]
            counter+=1
    for i in range(0,6):
        for j in range(i+1,6):
            for k in range(j+1,6):
                div[str(i)+str(j)+str(k)]=sgn*vect2[counter]
                counter+=1
    timedict['cvt_to_frz']=timedict.get('cvt_to_frz',0)+time.time()-start
    return frozenset(div.items())

def convert_to_str(min_div,obj):
    global timedict
    start=time.time()
    div=dict(min_div)
    divList=[]
    divList.append(div['d'])
    if obj=='curve':
        sgn=1
    elif obj=='div':
        sgn=-1
    for i in range(0,6):
        divList.append(sgn*div[str(i)])
    for i in range(0,6):
        for j in range(i+1,6):
            divList.append(sgn*div[str(i)+str(j)])
    for i in range(0,6):
        for j in range(i+1,6):
            for k in range(j+1,6):
                divList.append(sgn*div[str(i)+str(j)+str(k)])
    str_rep=' '.join((str(entry) for entry in divList))
    timedict['cvt_to_str']=timedict.get('cvt_to_str',0)+time.time()-start
    return str_rep

def find_S7_repre(div,order,obj):
    global timedict
    acted_by=dict()
    start=time.time()
    #this takes div and a value to minimize, gets the stabilizer of that value from another function...
    orbit_Candidates=set()
    orbit_Candidates.add(div)
    acted_by[div]=tuple((str(i) for i in range(7)))
    stabilizer_Of_Objectives=list()
    stabilizer_Of_Objectives.append('0123456')
    for objective in order[obj]:
        orbit_Candidates,stabilizer_Of_Objectives=add_objective(objective,orbit_Candidates,stabilizer_Of_Objectives,acted_by,obj)
        #print(orbit_Candidates,stabilizer_Of_Objectives,objective)
        if len(orbit_Candidates)==1 and len(stabilizer_Of_Objectives)==0:
            break
    if len(orbit_Candidates)!=1:
        print("error--too many representatives")
    timedict['find_S7_repre']=timedict.get('find_S7_repre',0)+time.time()-start
    final_repre=orbit_Candidates.pop()
    return final_repre,acted_by[final_repre]


def add_objective(objective,orbit_Candidates,stabilizer_Of_Objectives,acted_by,obj):
    global timedict
    start=time.time()
    objective_Stabilizer=compute_stab(objective)
    new_stab,transversals=compute_transversals(stabilizer_Of_Objectives, objective_Stabilizer)
    #print transversals
    #print new_stab
    minimizers=dict()
    candidate=orbit_Candidates.pop()
    minimizers['obj_val']=eval_obj(transversals[0],candidate,objective,obj)
    #minimizers['obj_val']=None
    minimizers['set']=set()
    minimizers['set'].add(grp_action(transversals[0],candidate,acted_by,obj))
    if len(transversals) >1:
        for elt in transversals[1:]:
            obj_val= eval_obj(elt,candidate,objective,obj)
            if obj_val==minimizers['obj_val']:
                minimizers['set'].add(grp_action(elt,candidate,acted_by,obj))
            elif obj_val < minimizers['obj_val']:
                minimizers['obj_val']=obj_val
                minimizers['set'].clear()
                minimizers['set'].add(grp_action(elt,candidate,acted_by,obj))
    for candidate in orbit_Candidates:
        for elt in transversals:
            obj_val= eval_obj(elt,candidate,objective,obj)
            if obj_val==minimizers['obj_val']:
                minimizers['set'].add(grp_action(elt,candidate,acted_by,obj))
            elif obj_val < minimizers['obj_val']:
                minimizers['obj_val']=obj_val
                minimizers['set'].clear()
                minimizers['set'].add(grp_action(elt,candidate,acted_by,obj))
    timedict['add_objective']=timedict.get('add_objective',0)+time.time()-start
    return minimizers['set'], new_stab
                    
def compute_transversals(sym1,sym2):
    global timedict
    start=time.time()
    #returns intersection of sym1 and sym2 as sym, and computes transversals for sym in sym1, returns in list.
    subG=list()
    subtransversals=list()
    for cycle in sym1:
        subtrans=list('e')
        splitOff=list()
        for chara in sym2:
            if chara in cycle:
                splitOff.append(chara)
                cycle=cycle.replace(chara,'')
        #print splitOff
        part2=''.join(splitOff)
        #print part2
        if len(cycle) >1:
            subG.append(cycle)
        if len(part2) >1:
            subG.append(part2)
        for i in range(1,1+min(len(cycle),len(part2))):
            #subtrans.extend(zip(*elt) for elt in product(combinations(cycle,i),permutations(part2,i)))
            for elt in product(combinations(cycle,i),combinations(part2,i)):
                #print 'elt is', elt
                #print 'zipping elt', zip(*elt)
                subtrans.append(tuple(zip(*elt)))
            #print subtrans
            #subtrans.extend() same thing if the above results in an error
            #tuple(zip())???
             
        subtransversals.append(subtrans)
    #print subtransversals
    transversals=tuple(tuple(chain(*elt)) for elt in product(*subtransversals)) #might have to tuple(chain) or frozenset(chain)
    #could just put this evaluations of transversals on the next line, and return it.
    timedict['compute_transversals']=timedict.get('compute_transversals',0)+time.time()-start
    return subG,transversals      
    
def grp_action(elt,div,acted_by,obj):
    global timedict
    start=time.time()
    prev_elt=acted_by[div]
    #computes and returns elt*div
    perm=dict()
    change6='e'
    for i in elt:
        #print i
        if i != 'e':
            if '6' in i:
                if change6 != 'e':
                    print("Error, 6 contained too many times")
                #change6=i
                j,k=i
                if j!='6':
                    change6 = j
                    perm[j]=j
                elif k != '6':
                    change6 = k
                    perm[k]=k
            else:
                j,k = i
                if j in perm or k in perm:
                    print("Error, transversals aren't disjoint transpositions")
                perm[j]=k
                perm[k]=j
    for letter in '012345':
        if letter not in perm:
            perm[letter]=letter
    
    if obj=='div':
        if change6 != 'e':
            div2=dict(div)
            div3=[]
            for coord in div:
                if change6 in coord[0]:
                    div3.append(coord)
                elif coord[0]=='d':
                    indices='012345'.replace(change6,'')
                    div3.append(tuple(('d',4*div2['d']-sum(div2[letter] for letter in indices))))
                else:
                    indices='012345'.replace(change6,'')
                    for letter in coord[0]:
                        indices=indices.replace(letter,'')
                    if len(coord[0])==1:
                        div3.append(tuple((coord[0],(len(indices)-1)*div2['d']-sum(div2[letter] for letter in indices))))
                    else:
                        div3.append(tuple((coord[0],(len(indices)-1)*div2['d']+div2[indices]-sum(div2[letter] for letter in indices))))
            div=frozenset(div3)
        div2=dict(div)
        div3=[]
        for coord in div:
            if coord[0] != 'd':
                sentTo=[]
                for letter in coord[0]:
                    sentTo.append(perm[letter])
                sentTo.sort()
                permuted=''.join(sentTo)
                div3.append(tuple((coord[0],div2[permuted])))
            else:
                div3.append(coord)
        timedict['grp_action']=timedict.get('grp_action',0)+time.time()-start
        #now, update acted_by
        new_div=frozenset(div3)
        start=time.time()
        if new_div not in acted_by:
            if change6 != 'e':
                perm[change6]='6'
                perm['6']=change6
            else:
                perm['6']='6'
            #new_elt=tuple((tuple((i[0],perm[i[1]])) for i in prev_elt)) #=tuple((perm[prev_elt[i]] for i in range(7)))
            #new_elt=frozenset((tuple((i[0],perm[i[1]])) for i in prev_elt))
            new_elt=tuple((perm[prev_elt[i]] for i in range(7)))
            acted_by[new_div]=new_elt
        timedict['record_gp_elt']=timedict.get('record_gp_elt',0)+time.time()-start
        
        #return frozenset(div3)
        return new_div
    
    elif obj!='curve':
        print("obj is not the right value in symmetry")
    
    if change6 != 'e':
        div2=dict(div)
        div3=[]
        for coord in div:
            if change6 in coord[0]:
                div3.append(coord)
            elif coord[0]=='d':
                #indices='012345'.replace(change6,'')
                valu=7*div2['d'] #7*coord[1]
                for coordi in div:
                    if change6 not in coordi[0]:
                        valu-=(4-len(coordi[0]))*coordi[1]
                div3.append(tuple(('d',valu)))
            elif len(coord[0])==1:
                indices='012345'.replace(change6,'')
                indices=indices.replace(coord[0],'')
                valu=div2['d']
                for index1,letter in enumerate(indices):
                    valu-=div2[letter]
                    for index2 in range(index1+1,len(indices)):
                        valu-=div2[letter+indices[index2]]
                        for index3 in range(index2+1,len(indices)):
                            valu-=div2[letter+indices[index2]+indices[index3]]
                div3.append(tuple((coord[0],valu)))
            else:
                indices='012345'.replace(change6,'')
                for letter in coord[0]:
                    indices=indices.replace(letter,'')
                div3.append(tuple((coord[0],div2[indices])))
        div=frozenset(div3)
    div2=dict(div)
    div3=[]
    for coord in div:
        if coord[0] != 'd':
            sentTo=[]
            for letter in coord[0]:
                sentTo.append(perm[letter])
            sentTo.sort()
            permuted=''.join(sentTo)
            div3.append(tuple((coord[0],div2[permuted])))
        else:
            div3.append(coord)
    timedict['grp_action']=timedict.get('grp_action',0)+time.time()-start
    
    #now, update acted_by
    new_div=frozenset(div3)
    start=time.time()
    if new_div not in acted_by:
        if change6 != 'e':
            perm[change6]='6'
            perm['6']=change6
        else:
            perm['6']='6'
        #new_elt=tuple((tuple((i[0],perm[i[1]])) for i in prev_elt)) #=tuple((perm[prev_elt[i]] for i in range(7)))
        #new_elt=frozenset((tuple((i[0],perm[i[1]])) for i in prev_elt))
        new_elt=tuple((perm[prev_elt[i]] for i in range(7)))
        acted_by[new_div]=new_elt
    timedict['record_gp_elt']=timedict.get('record_gp_elt',0)+time.time()-start
        
    #return frozenset(div3)
    return new_div


def compute_stab(objective):
    #returns the stabilizer of the objective, which will be the product of two symmetric groups, represented as lists
    #for now, just the following:
    if objective=='d':
        return '6'
    elif objective=='curve':
        return '56'
    else:
        return objective + '6'
    
def eval_obj(elt,div,objective,obj):
    global timedict
    start=time.time()
    #returns value of objective in elt*div, without computing the whole of elt*div
    
    #for now, just do the following:
    #div2=dict(grp_action(elt,div))
    #if objective=='d':
    
    
    #timedict['eval_obj_lazy']=timedict.get('eval_obj_lazy',0)+time.time()-start
    #return div2[objective]
    
    perm=dict()
    change6='e'
    for i in elt:
        #print i
        if i != 'e':
            if '6' in i:
                if change6 != 'e':
                    print("Error, 6 contained too many times")
                #change6=i
                j,k=i
                if j!='6':
                    change6 = j
                    perm[j]=j
                elif k != '6':
                    change6 = k
                    perm[k]=k
            else:
                j,k = i
                if j in perm or k in perm:
                    print("Error, transversals aren't disjoint transpositions")
                perm[j]=k
                perm[k]=j
    for letter in '012345':
        if letter not in perm:
            perm[letter]=letter
    
    if obj=='div':
        if change6 != 'e':
            if objective!='d':
                print("ERROR OBJECTIVE NOT AS EXPECTED")
            div2=dict(div)
            #indices='012345'.replace(change6,'')
            timedict['eval_obj_lazy']=timedict.get('eval_obj_lazy',0)+time.time()-start
            return 4*div2['d']-sum(div2[letter] for letter in '012345'.replace(change6,''))
        elif objective=='d':
            div2=dict(div)
            timedict['eval_obj_lazy']=timedict.get('eval_obj_lazy',0)+time.time()-start
            return div2['d']
        else:
            div2=dict(div)
            sentTo=[]
            for letter in objective:
                sentTo.append(perm[letter])
            sentTo.sort()
            timedict['eval_obj_lazy']=timedict.get('eval_obj_lazy',0)+time.time()-start
            return div2[''.join(sentTo)]
    
    elif obj!='curve':
        print("error obj wasn't right in symmetry")
    
    if change6 != 'e':
        if objective!='d':
            print("ERROR OBJECTIVE NOT AS EXPECTED")
        div2=dict(div)
        valu=7*div2['d'] #only use of div2, could probably be improved.
        for coordi in div:
            if change6 not in coordi[0]:
                valu-=(4-len(coordi[0]))*coordi[1]
        timedict['eval_obj_lazy']=timedict.get('eval_obj_lazy',0)+time.time()-start
        return valu
    elif objective=='d':
        div2=dict(div)
        timedict['eval_obj_lazy']=timedict.get('eval_obj_lazy',0)+time.time()-start
        return div2['d']
    elif objective=='curve':
        ideal_ht=0
        #maxpt=0 #use this if not using div?  Maybe.  Kinda breaks symmetry, err doesn't guarantee unique representative
        for coordi in div:
            if perm['5'] in coordi[0]:
                ideal_ht+=(5-len(coordi[0]))*coordi[1]
                #if coordi[1]>0:
                #    if 5-len(coordi[0])>maxpt:
                #        maxpt=5-len(coordi[0])
        return ideal_ht#-maxpt
    else:
        div2=dict(div)
        sentTo=[]
        for letter in objective:
            sentTo.append(perm[letter])
        sentTo.sort()
        timedict['eval_obj_lazy']=timedict.get('eval_obj_lazy',0)+time.time()-start
        return div2[''.join(sentTo)]








#######END SECTION THAT IS FINDING SYMMETRY





    
    
    
    
def convert_to_dict(vect2):
    counter=0
    div=dict()
    div['d']=vect2[counter]
    counter+=1
    div[1]=dict()
    div[2]=dict()
    div[3]=dict()
    for i in range(0,6):
        div[1][str(i)]=-vect2[counter]
        counter+=1
    for i in range(0,6):
        for j in range(i+1,6):
            div[2][str(i)+str(j)]=-vect2[counter]
            counter+=1
    for i in range(0,6):
        for j in range(i+1,6):
            for k in range(j+1,6):
                div[3][str(i)+str(j)+str(k)]=-vect2[counter]
                counter+=1
    return div
        

def construct_monomial_coeffs(div): #div is a dictionary giving the divisor
    global timedict
    start=time.time()
    #point i corresponds to the vanishing of every linear monomial but xi
    #similarly, line ij corresponds to vanishing of every lin monomial but xi, xj
    #lastly, plane ijk = vanishing of every lin monomial but xi, xj, xk
    #so, if div[1]["i"] is point i, div[2]["ij"] is line ij, div[3]['ijk'] is plane ijk, and div['d']=degree, then
    #if d=div['d'], mi=div[1]['i'], mij=div[2]['ij'], mijk=div[3]['ijk'], and a_y0_b_y1_b_#y2_...y4 is coeff of corresponding monomial x0^(y0)...x4^(y4),
    #then see that to belong to the linear system of div, if a_y0_b_y1_b_#y2_...y4 is nonzero, the yi need to satisfy 26 equations/inequalities:
    # letting i,j,k,h,l be 0,1,2,3,4 in any order
    # sum(yi)==d
    # 0 <= yi <= d-mi  (there are 5 of these, 10 if count both directions)   EQUIV   d >= sum(yj j!=i) >= mi
    # yi + yj <= d-mij  (there are 10 of these)   EQUIV   sum(yk k!=i,j) >= mij
    # yi + yj + yk <= d-mijk  (there are 10 of these)   EQUIV   yh + yl >= mijk
    #these equivalent representations help if, say, we set y4=d-sum(yi i!=4), and iterate over interger points of the corresponding polytope to create the coefficient variables
    #So, set y4=d-sum(yi i!=4), and use as constraints the inequalities above that do not contain y4.
    acoeffs=list()
    deg=div['d']
    for y0 in range(0,1+(deg-div[1]['0'])): #need to make sure that range returns an empty list if the first bound is larger than the second
        for y1 in range(max(0,div[3]['234']-y0),1+min(deg-div[1]['1'], deg-div[2]['01']-y0)):
            for y2 in range(max(0, div[3]['134']-y0, div[3]['034']-y1, div[2]['34']-y0-y1), 1+min(deg-div[1]['2'], deg-div[2]['02']-y0, deg-div[2]['12']-y1, deg-div[3]['012']-y0-y1)):
                lower3=max(0, div[3]['014']-y2, div[3]['024']-y1, div[3]['124']-y0, div[2]['04']-y1-y2, div[2]['14']-y0-y2, div[2]['24']-y0-y1, div[1]['4']-y0-y1-y2)
                upper3=min(deg-y0-y1-y2, deg-div[1]['3'], deg-div[2]['03']-y0, deg-div[2]['13']-y1, deg-div[2]['23']-y2, deg-div[3]['013']-y0-y1, deg-div[3]['023']-y0-y2, deg-div[3]['123']-y1-y2)
                for y3 in range(lower3,1+upper3):
                    y4 = deg-y0-y1-y2-y3
                    coeff = 'a'+str(y0)+'b'+str(y1)+'b'+str(y2)+'b'+str(y3)+'b'+str(y4)
                    acoeffs.append(coeff)
    print("finished constructing coeffs, there are", len(acoeffs))
    timedict['acoeffs']=timedict.get('acoeffs',0)+time.time()-start
    return acoeffs



#'''
def add_conds1(deg,div,conditions,acoeffs,y4,n1):
    global timedict
    start=time.time()
    fixed_pts=tuple((i1 for i1 in range(0,5) if i1!=y4))
    timedict['y0']=timedict.get('y0',0)
    timedict['y1']=timedict.get('y1',0)
    timedict['y2']=timedict.get('y2',0)
    timedict['y3']=timedict.get('y3',0)
    timedict['sum_cond']=timedict.get('sum_cond',0)
    copy0_acoeffs=tuple((tuple((int(elt) for i1,elt in enumerate(coeff[1:].split('b')) if i1!=y4))+tuple((i2,1)) for i2,coeff in enumerate(acoeffs)))
   
    conds_to_check=dict()
    new_conds=list((list(),list(),list()))
    old_conds=list((list(),list()))
    if y4==4:
        new_conds[2].append(tuple((tuple((0,1,2)),div[1]['5'])))
        conds_to_check[tuple((0,1,2,2))]=0
    else:
        old_conds[1].append(tuple((tuple((0,1,2)),div[1]['5'])))
    
    for i1,index in enumerate(fixed_pts):
        if div[2][str(index)+'5']>=1:
            if y4==4:
                min_val=minimize_para(str(index)+'5',div,deg)
                if min_val>=1:
                    if i1!=3:
                        conds_to_check[tuple((i2 for i2 in (0,1,2) if i2!=i1))+(2,)]=div[2][str(index)+'5']-min_val
                        new_conds[2].append(tuple((tuple((i2 for i2 in (0,1,2) if i2!=i1)),div[2][str(index)+'5'])))  #believe can use this to set upper3, and not all conds, unlike for lower3
                    else:
                        conds_to_check[tuple((0,1,1))]=div[2][str(index)+'5']-min_val
                        new_conds[1].append(tuple((tuple((0,1)),div[2][str(index)+'5'])))
            elif y4==3:
                if i1!=3:
                    old_conds[1].append(tuple((tuple((i2 for i2 in (0,1,2) if i2!=i1)),div[2][str(index)+'5'])))
                else: #if i1==3:
                    min_val=minimize_para(str(index)+'5',div,deg)
                    if min_val>=1:
                        conds_to_check[tuple((0,1,1))]=div[2][str(index)+'5']-min_val
                        new_conds[1].append(tuple((tuple((0,1)),div[2][str(index)+'5'])))
            else: #y4==2:
                if i1!=3:
                    old_conds[1].append(tuple((tuple((i2 for i2 in (0,1,2) if i2!=i1)),div[2][str(index)+'5'])))
                else: #if i1==3:
                    old_conds[0].append(tuple((tuple((0,1)),div[2][str(index)+'5'])))
        
        for i2,index2 in enumerate(fixed_pts[i1+1:]):
            if div[3][str(index)+str(index2)+'5']>=1:
                if y4==4:
                    min_val=minimize_para(str(index)+str(index2)+'5',div,deg)
                    if min_val>=1:
                        if i1==2:
                            conds_to_check[tuple((0,0))]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[0].append(tuple(((0,),div[3]['235'])))
                        elif i1+i2==2:
                            conds_to_check[tuple((i3 for i3 in (0,1) if i3!=i1))+(1,)]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[1].append(tuple((tuple((i3 for i3 in (0,1) if i3!=i1)),div[3][str(index)+str(index2)+'5'])))
                        else:
                            conds_to_check[tuple((i3 for i3 in (0,1,2) if i3!=i1 and i3!=i1+i2+1))+(2,)]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[2].append(tuple((tuple((i3 for i3 in (0,1,2) if i3!=i1 and i3!=i1+i2+1)),div[3][str(index)+str(index2)+'5'])))
                elif y4==3:
                    if i1==2:
                        min_val=minimize_para(str(index)+str(index2)+'5',div,deg)
                        if min_val>=1:
                            conds_to_check[tuple((0,0))]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[0].append(tuple(((0,),div[3]['245'])))
                    elif i1+i2==2:
                        min_val=minimize_para(str(index)+str(index2)+'5',div,deg)
                        if min_val>=1:
                            conds_to_check[tuple((i3 for i3 in (0,1) if i3!=i1))+(1,)]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[1].append(tuple((tuple((i3 for i3 in (0,1) if i3!=i1)),div[3][str(index)+str(index2)+'5'])))
                    else:
                        old_conds[1].append(tuple((tuple((i3 for i3 in (0,1,2) if i3!=i1 and i3!=i1+i2+1)),div[3][str(index)+str(index2)+'5'])))
                else: #y4==2:
                    if i1==2:
                        min_val=minimize_para(str(index)+str(index2)+'5',div,deg)
                        if min_val>=1:
                            conds_to_check[tuple((0,0))]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[0].append(tuple(((0,),div[3]['345'])))
                    elif i1+i2==2:
                        old_conds[0].append(tuple((tuple((i3 for i3 in (0,1) if i3!=i1)),div[3][str(index)+str(index2)+'5'])))
                    else:
                        old_conds[1].append(tuple((tuple((i3 for i3 in (0,1,2) if i3!=i1 and i3!=i1+i2+1)),div[3][str(index)+str(index2)+'5'])))
    for i1,lis in enumerate(reversed(old_conds)):
        yi=3-i1
        for elt in lis:
            copy0_acoeffs=tuple((coeff for coeff in copy0_acoeffs if coeff[yi]+sum(coeff[i2] for i2 in elt[0])>=elt[1]))
    
    max_power=0
    for coeff in copy0_acoeffs:
        for numbe in coeff[:4]:
            if numbe>max_power:
                max_power=numbe
    binom_array=tuple((tuple((binomial(i1,i2) for i2 in range(0,i1+1))) for i1 in range(0,max_power+1)))
    
    l2=str(fixed_pts[-2]) #fixed_str[-2]
    l3=str(fixed_pts[-1]) #fixed_str[-1]
    print(time.time()-start,"is amount of time for loop set up")
    for y0 in range(0,1+deg-div[1]['0']):
        start0=time.time()
        if y0>1:
            copy0_acoeffs=tuple((coeff[:-1]+(binom_array[coeff[0]][y0],) for coeff in copy0_acoeffs if coeff[0]>=y0))
            #copy0_acoeffs=tuple(((*coeff[:-1],binom_array[coeff[0]][y0]) for coeff in copy0_acoeffs if coeff[0]>=y0))
        elif y0==1:
            copy0_acoeffs=tuple((coeff[:-1]+(coeff[0],) for coeff in copy0_acoeffs if coeff[0]))#>=1))
            #copy0_acoeffs=tuple(((*coeff[:-1],coeff[0]) for coeff in copy0_acoeffs if coeff[0]>=1))
        copy1_acoeffs=copy0_acoeffs
        ###copy1_acoeffs=tuple((coeff[1:5]+(coeff[-1],) for coeff in copy0_acoeffs))
        
        
        if new_conds[1] or new_conds[2]:
            if new_conds[0] and conds_to_check[tuple((0,0))]<=y0<div[3][l2+l3+'5']:
                add_condi1=False
            else:
                add_condi1=True
            upper1=1+deg-max(div[1]['1'], div[2]['01']+y0)
        else:
            add_condi1=False
            upper1=min(1+deg-max(div[1]['1'],div[2]['01']+y0),new_conds[0][0][1]-y0)
        timedict['y0']+=time.time()-start0
        
        for y1 in range(0,upper1):
            start1=time.time()
            if y1>1:
                copy1_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[1]][y1],) for coeff in copy1_acoeffs if coeff[1]>=y1))
                #copy1_acoeffs=tuple(((*coeff[:-1],coeff[-2]*binom_array[coeff[1]][y1]) for coeff in copy1_acoeffs if coeff[1]>=y1))
                ###copy1_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[0]][y1],) for coeff in copy1_acoeffs if coeff[0]>=y1))
            elif y1==1:
                copy1_acoeffs=tuple((coeff+(coeff[-1]*coeff[1],) for coeff in copy1_acoeffs if coeff[1]))#>=1))
                #copy1_acoeffs=tuple(((*coeff,coeff[-1]*coeff[1]) for coeff in copy1_acoeffs if coeff[1]>=1))
                ###copy1_acoeffs=tuple((coeff+(coeff[-1]*coeff[0],) for coeff in copy1_acoeffs if coeff[0]>=1))
            
            ys=tuple((y0,y1))
            if old_conds[0]:
                lower2=max(0,max(elt[1]-sum(ys[i1] for i1 in elt[0]) for elt in old_conds[0]))
            else:
                lower2=0
            
            if new_conds[0]:
                if add_condi1:                   
                    if conds_to_check[tuple((0,0))]==y0+y1:
                        add_condi1=False
                else:
                    if y0+y1==div[3][l2+l3+'5']:
                        add_condi1=True
            
            if add_condi1 and not new_conds[2]:
                add_condi2=False
                upper2=min(1+deg-max(div[1][l2], div[2]['0'+l2]+y0, div[2]['1'+l2]+y1, div[3]['01'+l2]+y0+y1),max(elt[1]-sum(ys[i1] for i1 in elt[0]) for elt in new_conds[1]))
            else:
                add_condi2=True
                upper2=1+deg-max(div[1][l2], div[2]['0'+l2]+y0, div[2]['1'+l2]+y1, div[3]['01'+l2]+y0+y1)
            
            
            if lower2<=1:
                copy2_acoeffs=copy1_acoeffs
                ###copy2_acoeffs=tuple((coeff[1:4]+(coeff[-1],) for coeff in copy1_acoeffs))
            else:
                copy2_acoeffs=tuple((coeff+(1,) for coeff in copy1_acoeffs))
                ###copy2_acoeffs=tuple((coeff[1:4]+(coeff[-1],1) for coeff in copy1_acoeffs))
                
            timedict['y1']+=time.time()-start1
            
            for y2 in range(lower2,upper2):
                start2=time.time()
                if y2>1:
                    copy2_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[2]][y2],) for coeff in copy2_acoeffs if coeff[2]>=y2))
                    #copy2_acoeffs=tuple(((*coeff[:-1],coeff[-2]*binom_array[coeff[2]][y2]) for coeff in copy2_acoeffs if coeff[2]>=y2))
                    ###copy2_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[0]][y2],) for coeff in copy2_acoeffs if coeff[0]>=y2))
                elif y2==1:
                    copy2_acoeffs=tuple((coeff+(coeff[-1]*coeff[2],) for coeff in copy2_acoeffs if coeff[2]))#>=1))
                    #copy2_acoeffs=tuple(((*coeff,coeff[-1]*coeff[2]) for coeff in copy2_acoeffs if coeff[2]>=1))
                    ###copy2_acoeffs=tuple((coeff+(coeff[-1]*coeff[0],) for coeff in copy2_acoeffs if coeff[0]>=1))
                
                
                if add_condi1 and new_conds[1]:
                    if add_condi2:#################################################################################################
                        if any((conds_to_check[elt[0]+(1,)]<=y2+sum(ys[i1] for i1 in elt[0])<elt[1] for elt in new_conds[1])):
                            add_condi2=False
                    elif new_conds[2]: #probably just a time saver over using else.  If not new_conds[2], then from above already would have restricted y2 so that none of these would trigger???????????????????????????? idk look into that.
                        if not any((elt[1]>y2+sum(ys[i1] for i1 in elt[0])>=conds_to_check[elt[0]+(1,)] for elt in new_conds[1])):
                            add_condi2=True
                    else: #could just use original else, but this might make it marginally faster.  
                        if not any((y2+sum(ys[i1] for i1 in elt[0])>=conds_to_check[elt[0]+(1,)] for elt in new_conds[1])):
                            add_condi2=True
                
                ys=tuple((y0,y1,y2))
                if old_conds[1]:
                    lower3=max(0,max(elt[1]-sum(ys[i1] for i1 in elt[0]) for elt in old_conds[1]))
                else:
                    lower3=0        
                    
                
                
                if add_condi1 and add_condi2:################################################################
                    if new_conds[2]:
                        upper3=min(-y0-y1-y2+max(div[1]['5'],div[2]['05']+y0,div[2]['15']+y1,div[2][l2+'5']+y2,div[3]['015']+y0+y1,div[3]['0'+l2+'5']+y0+y2,div[3]['1'+l2+'5']+y1+y2),1+deg-max(y0+y1+y2, div[1][l3], div[2]['0'+l3]+y0, div[2]['1'+l3]+y1, div[2]['2'+l3]+y2, div[3]['01'+l3]+y0+y1, div[3]['02'+l3]+y0+y2, div[3]['12'+l3]+y1+y2))
                        #upper3=min(max(elt[1]-sum(ys[i1] for i1 in elt[0]) for elt in new_conds[2]),1+deg-max(y0+y1+y2, div[1][l3], div[2]['0'+l3]+y0, div[2]['1'+l3]+y1, div[2]['2'+l3]+y2, div[3]['01'+l3]+y0+y1, div[3]['02'+l3]+y0+y2, div[3]['12'+l3]+y1+y2))
                        #lower3=max(lower3,max(conds_to_check[elt[0]+(2,)]-sum(ys[i1] for i1 in elt[0]) for elt in new_conds[2]))
                        #not useful because conds_to_check[5] is always 0
                    else:
                        upper3=lower3 #upper3=0
                    #upper3=min(-y0-y1-y2+max(div[1]['5'],div[2]['05']+y0,div[2]['15']+y1,div[2][l2+'5']+y2,div[3]['015']+y0+y1,div[3]['0'+l2+'5']+y0+y2,div[3]['1'+l2+'5']+y1+y2),1+deg-max(y0+y1+y2, div[1][l3], div[2]['0'+l3]+y0, div[2]['1'+l3]+y1, div[2]['2'+l3]+y2, div[3]['01'+l3]+y0+y1, div[3]['02'+l3]+y0+y2, div[3]['12'+l3]+y1+y2))
                else:####################################################################################
                    upper3=1+deg-max(y0+y1+y2, div[1][l3], div[2]['0'+l3]+y0, div[2]['1'+l3]+y1, div[2][l2+l3]+y2, div[3]['01'+l3]+y0+y1, div[3]['0'+l2+l3]+y0+y2, div[3]['1'+l2+l3]+y1+y2)
                
                if lower3<=1:
                    copy3_acoeffs=copy2_acoeffs
                    ###copy3_acoeffs=tuple((coeff[1:3]+(coeff[-1],) for coeff in copy2_acoeffs))
                else:
                    copy3_acoeffs=tuple((coeff+(1,) for coeff in copy2_acoeffs))
                    ###copy3_acoeffs=tuple((coeff[1:3]+(coeff[-1],1) for coeff in copy2_acoeffs))
                
                timedict['y2']+=time.time()-start2
                
                for y3 in range(lower3,upper3):
                    start3=time.time()
                    if add_condi1 and add_condi2:
                        if any((conds_to_check[elt[0]+(2,)]<=y3+sum(ys[i1] for i1 in elt[0])<elt[1] for elt in new_conds[2])):
                            if y3>1:
                                copy3_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[3]][y3],) for coeff in copy3_acoeffs if coeff[3]>=y3))
                                ###copy3_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[0]][y3],) for coeff in copy3_acoeffs if coeff[0]>=y3))
                                #copy3_acoeffs=tuple(((*coeff[:-1],coeff[-2]*binom_array[coeff[3]][y3]) for coeff in copy3_acoeffs if coeff[3]>=y3))
                                start4=time.time()
                                conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs})
                                ###conditions.update({(n1,coeffi[1]):coeffi[-1] for coeffi in copy3_acoeffs})
                                timedict['sum_cond']+=time.time()-start4
                            elif y3==1:
                                copy3_acoeffs=tuple((coeff+(coeff[-1]*coeff[3],) for coeff in copy3_acoeffs if coeff[3]))#>=1))
                                ###copy3_acoeffs=tuple((coeff+(coeff[-1]*coeff[0],) for coeff in copy3_acoeffs if coeff[0]>=1))
                                #copy3_acoeffs=tuple(((*coeff,coeff[-1]*coeff[3]) for coeff in copy3_acoeffs if coeff[3]>=1))
                                start4=time.time()
                                conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs})
                                ###conditions.update({(n1,coeffi[1]):coeffi[-1] for coeffi in copy3_acoeffs})
                                timedict['sum_cond']+=time.time()-start4
                            else:
                                start4=time.time()
                                conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs})
                                ###conditions.update({(n1,coeffi[1]):coeffi[-1] for coeffi in copy3_acoeffs})
                                timedict['sum_cond']+=time.time()-start4
                            n1+=1
                        elif y3==1:
                            copy3_acoeffs=tuple((coeff+(1,) for coeff in copy3_acoeffs))
                            #print("y3=1 wasn't used for conds")
                        #else:
                        #    print(y3,"wasn't used for conds")
                    else:
                        if y3>1:
                            copy3_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[3]][y3],) for coeff in copy3_acoeffs if coeff[3]>=y3))
                            ###copy3_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[0]][y3],) for coeff in copy3_acoeffs if coeff[0]>=y3))
                            #copy3_acoeffs=tuple(((*coeff[:-1],coeff[-2]*binom_array[coeff[3]][y3]) for coeff in copy3_acoeffs if coeff[3]>=y3))
                            start4=time.time()
                            conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs})
                            ###conditions.update({(n1,coeffi[1]):coeffi[-1] for coeffi in copy3_acoeffs})
                            #conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs if GF(2)(coeffi[-1])!=GF(2)(0)})
                            timedict['sum_cond']+=time.time()-start4
                        elif y3==1:
                            copy3_acoeffs=tuple((coeff+(coeff[-1]*coeff[3],) for coeff in copy3_acoeffs if coeff[3]))#>=1))
                            ###copy3_acoeffs=tuple((coeff+(coeff[-1]*coeff[0],) for coeff in copy3_acoeffs if coeff[0]>=1))
                            #copy3_acoeffs=tuple(((*coeff,coeff[-1]*coeff[3]) for coeff in copy3_acoeffs if coeff[3]>=1))
                            start4=time.time()
                            conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs})
                            ###conditions.update({(n1,coeffi[1]):coeffi[-1] for coeffi in copy3_acoeffs})
                            timedict['sum_cond']+=time.time()-start4
                        else:
                            start4=time.time()
                            conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs})
                            ###conditions.update({(n1,coeffi[1]):coeffi[-1] for coeffi in copy3_acoeffs})
                            timedict['sum_cond']+=time.time()-start4
                        n1+=1
                    timedict['y3']+=time.time()-start3   
    timedict['add_condssss']=timedict.get('add_condssss',0)+time.time()-start
    print('add_condsss took', time.time()-start,'seconds')
    return n1


#'''
def add_conds2(deg,div,conditions,acoeffs,y4,n1,charac):
    global timedict
    start=time.time()
    fixed_pts=tuple((i1 for i1 in range(0,5) if i1!=y4))
    timedict['y0']=timedict.get('y0',0)
    timedict['y1']=timedict.get('y1',0)
    timedict['y2']=timedict.get('y2',0)
    timedict['y3']=timedict.get('y3',0)
    timedict['sum_cond']=timedict.get('sum_cond',0)
    copy0_acoeffs=tuple((tuple((int(elt) for i1,elt in enumerate(coeff[1:].split('b')) if i1!=y4))+tuple((i2,1)) for i2,coeff in enumerate(acoeffs)))
   
    conds_to_check=dict()
    new_conds=list((list(),list(),list()))
    old_conds=list((list(),list()))
    if y4==4:
        new_conds[2].append(tuple((tuple((0,1,2)),div[1]['5'])))
        conds_to_check[tuple((0,1,2,2))]=0
    else:
        old_conds[1].append(tuple((tuple((0,1,2)),div[1]['5'])))
    
    for i1,index in enumerate(fixed_pts):
        if div[2][str(index)+'5']>=1:
            if y4==4:
                min_val=minimize_para(str(index)+'5',div,deg)
                if min_val>=1:
                    if i1!=3:
                        conds_to_check[tuple((i2 for i2 in (0,1,2) if i2!=i1))+(2,)]=div[2][str(index)+'5']-min_val
                        new_conds[2].append(tuple((tuple((i2 for i2 in (0,1,2) if i2!=i1)),div[2][str(index)+'5'])))  #believe can use this to set upper3, and not all conds, unlike for lower3
                    else:
                        conds_to_check[tuple((0,1,1))]=div[2][str(index)+'5']-min_val
                        new_conds[1].append(tuple((tuple((0,1)),div[2][str(index)+'5'])))
            elif y4==3:
                if i1!=3:
                    old_conds[1].append(tuple((tuple((i2 for i2 in (0,1,2) if i2!=i1)),div[2][str(index)+'5'])))
                else: #if i1==3:
                    min_val=minimize_para(str(index)+'5',div,deg)
                    if min_val>=1:
                        conds_to_check[tuple((0,1,1))]=div[2][str(index)+'5']-min_val
                        new_conds[1].append(tuple((tuple((0,1)),div[2][str(index)+'5'])))
            else: #y4==2:
                if i1!=3:
                    old_conds[1].append(tuple((tuple((i2 for i2 in (0,1,2) if i2!=i1)),div[2][str(index)+'5'])))
                else: #if i1==3:
                    old_conds[0].append(tuple((tuple((0,1)),div[2][str(index)+'5'])))
        
        for i2,index2 in enumerate(fixed_pts[i1+1:]):
            if div[3][str(index)+str(index2)+'5']>=1:
                if y4==4:
                    min_val=minimize_para(str(index)+str(index2)+'5',div,deg)
                    if min_val>=1:
                        if i1==2:
                            conds_to_check[tuple((0,0))]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[0].append(tuple(((0,),div[3]['235'])))
                        elif i1+i2==2:
                            conds_to_check[tuple((i3 for i3 in (0,1) if i3!=i1))+(1,)]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[1].append(tuple((tuple((i3 for i3 in (0,1) if i3!=i1)),div[3][str(index)+str(index2)+'5'])))
                        else:
                            conds_to_check[tuple((i3 for i3 in (0,1,2) if i3!=i1 and i3!=i1+i2+1))+(2,)]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[2].append(tuple((tuple((i3 for i3 in (0,1,2) if i3!=i1 and i3!=i1+i2+1)),div[3][str(index)+str(index2)+'5'])))
                elif y4==3:
                    if i1==2:
                        min_val=minimize_para(str(index)+str(index2)+'5',div,deg)
                        if min_val>=1:
                            conds_to_check[tuple((0,0))]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[0].append(tuple(((0,),div[3]['245'])))
                    elif i1+i2==2:
                        min_val=minimize_para(str(index)+str(index2)+'5',div,deg)
                        if min_val>=1:
                            conds_to_check[tuple((i3 for i3 in (0,1) if i3!=i1))+(1,)]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[1].append(tuple((tuple((i3 for i3 in (0,1) if i3!=i1)),div[3][str(index)+str(index2)+'5'])))
                    else:
                        old_conds[1].append(tuple((tuple((i3 for i3 in (0,1,2) if i3!=i1 and i3!=i1+i2+1)),div[3][str(index)+str(index2)+'5'])))
                else: #y4==2:
                    if i1==2:
                        min_val=minimize_para(str(index)+str(index2)+'5',div,deg)
                        if min_val>=1:
                            conds_to_check[tuple((0,0))]=div[3][str(index)+str(index2)+'5']-min_val
                            new_conds[0].append(tuple(((0,),div[3]['345'])))
                    elif i1+i2==2:
                        old_conds[0].append(tuple((tuple((i3 for i3 in (0,1) if i3!=i1)),div[3][str(index)+str(index2)+'5'])))
                    else:
                        old_conds[1].append(tuple((tuple((i3 for i3 in (0,1,2) if i3!=i1 and i3!=i1+i2+1)),div[3][str(index)+str(index2)+'5'])))
    for i1,lis in enumerate(reversed(old_conds)):
        yi=3-i1
        for elt in lis:
            copy0_acoeffs=tuple((coeff for coeff in copy0_acoeffs if coeff[yi]+sum(coeff[i2] for i2 in elt[0])>=elt[1]))
    
    max_power=0
    for coeff in copy0_acoeffs:
        for numbe in coeff[:4]:
            if numbe>max_power:
                max_power=numbe
    #binom_array=tuple((tuple((binomial(i1,i2)%charac for i2 in range(0,i1+1))) for i1 in range(0,max_power+1)))
    #binom_array=tuple((tuple((GF(charac)(binomial(i1,i2)%charac) for i2 in range(0,i1+1))) for i1 in range(0,max_power+1)))
    binom_array=tuple((tuple((GF(charac)(binomial(i1,i2)) for i2 in range(0,i1+1))) for i1 in range(0,max_power+1)))
    
    l2=str(fixed_pts[-2]) #fixed_str[-2]
    l3=str(fixed_pts[-1]) #fixed_str[-1]
    print(time.time()-start,"is amount of time for loop set up")
    for y0 in range(0,1+deg-div[1]['0']):
        start0=time.time()
        if y0>1:
            copy0_acoeffs=tuple((coeff[:-1]+(binom_array[coeff[0]][y0],) for coeff in copy0_acoeffs if coeff[0]>=y0))
            #copy0_acoeffs=tuple(((*coeff[:-1],binom_array[coeff[0]][y0]) for coeff in copy0_acoeffs if coeff[0]>=y0))
        elif y0==1:
            #copy0_acoeffs=tuple((coeff[:-1]+(coeff[0]%charac,) for coeff in copy0_acoeffs if coeff[0]))
            copy0_acoeffs=tuple((coeff[:-1]+(binom_array[coeff[0]][1],) for coeff in copy0_acoeffs if coeff[0]))#>=1))
            #copy0_acoeffs=tuple(((*coeff[:-1],coeff[0]) for coeff in copy0_acoeffs if coeff[0]))
        copy1_acoeffs=tuple((coeff for coeff in copy0_acoeffs if coeff[-1]))
        
        
        if new_conds[1] or new_conds[2]:
            if new_conds[0] and conds_to_check[tuple((0,0))]<=y0<div[3][l2+l3+'5']:
                add_condi1=False
            else:
                add_condi1=True
            upper1=1+deg-max(div[1]['1'], div[2]['01']+y0)
        else:
            add_condi1=False
            upper1=min(1+deg-max(div[1]['1'],div[2]['01']+y0),new_conds[0][0][1]-y0)
        timedict['y0']+=time.time()-start0
        
        for y1 in range(0,upper1):
            start1=time.time()
            if y1>1:
                copy1_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[1]][y1],) for coeff in copy1_acoeffs if coeff[1]>=y1))
                #copy1_acoeffs=tuple(((*coeff[:-1],coeff[-2]*binom_array[coeff[1]][y1]) for coeff in copy1_acoeffs if coeff[1]>=y1))
            elif y1==1:
                #copy1_acoeffs=tuple((coeff+(coeff[-1]*(coeff[1]%charac),) for coeff in copy1_acoeffs if coeff[1]))
                copy1_acoeffs=tuple((coeff+(coeff[-1]*binom_array[coeff[1]][1],) for coeff in copy1_acoeffs if coeff[1]))#>=1))
                #copy1_acoeffs=tuple(((*coeff,coeff[-1]*coeff[1]) for coeff in copy1_acoeffs if coeff[1]))
            
            ys=tuple((y0,y1))
            if old_conds[0]:
                lower2=max(0,max(elt[1]-sum(ys[i1] for i1 in elt[0]) for elt in old_conds[0]))
            else:
                lower2=0
            
            if new_conds[0]:
                if add_condi1:                   
                    if conds_to_check[tuple((0,0))]==y0+y1:
                        add_condi1=False
                else:
                    if y0+y1==div[3][l2+l3+'5']:
                        add_condi1=True
            
            if add_condi1 and not new_conds[2]:
                add_condi2=False
                upper2=min(1+deg-max(div[1][l2], div[2]['0'+l2]+y0, div[2]['1'+l2]+y1, div[3]['01'+l2]+y0+y1),max(elt[1]-sum(ys[i1] for i1 in elt[0]) for elt in new_conds[1]))
            else:
                add_condi2=True
                upper2=1+deg-max(div[1][l2], div[2]['0'+l2]+y0, div[2]['1'+l2]+y1, div[3]['01'+l2]+y0+y1)
            
            
            if lower2<=1:
                copy2_acoeffs=tuple((coeff for coeff in copy1_acoeffs if coeff[-1]))
            else:
                copy2_acoeffs=tuple((coeff+(1,) for coeff in copy1_acoeffs if coeff[-1]))
                
            timedict['y1']+=time.time()-start1
            
            for y2 in range(lower2,upper2):
                start2=time.time()
                if y2>1:
                    copy2_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[2]][y2],) for coeff in copy2_acoeffs if coeff[2]>=y2))
                    #copy2_acoeffs=tuple(((*coeff[:-1],coeff[-2]*binom_array[coeff[2]][y2]) for coeff in copy2_acoeffs if coeff[2]>=y2))
                elif y2==1:
                    #copy2_acoeffs=tuple((coeff+(coeff[-1]*(coeff[2]%charac),) for coeff in copy2_acoeffs if coeff[2]))
                    copy2_acoeffs=tuple((coeff+(coeff[-1]*binom_array[coeff[2]][1],) for coeff in copy2_acoeffs if coeff[2]))#>=1))
                    #copy2_acoeffs=tuple(((*coeff,coeff[-1]*coeff[2]) for coeff in copy2_acoeffs if coeff[2]))
                
                
                if add_condi1 and new_conds[1]:
                    if add_condi2:#################################################################################################
                        if any((conds_to_check[elt[0]+(1,)]<=y2+sum(ys[i1] for i1 in elt[0])<elt[1] for elt in new_conds[1])):
                            add_condi2=False
                    elif new_conds[2]: #probably just a time saver over using else.  If not new_conds[2], then from above already would have restricted y2 so that none of these would trigger???????????????????????????? idk look into that.
                        if not any((elt[1]>y2+sum(ys[i1] for i1 in elt[0])>=conds_to_check[elt[0]+(1,)] for elt in new_conds[1])):
                            add_condi2=True
                    else: #could just use original else, but this might make it marginally faster.  
                        if not any((y2+sum(ys[i1] for i1 in elt[0])>=conds_to_check[elt[0]+(1,)] for elt in new_conds[1])):
                            add_condi2=True
                
                ys=tuple((y0,y1,y2))
                if old_conds[1]:
                    lower3=max(0,max(elt[1]-sum(ys[i1] for i1 in elt[0]) for elt in old_conds[1]))
                else:
                    lower3=0        
                    
                
                
                if add_condi1 and add_condi2:################################################################
                    if new_conds[2]:
                        upper3=min(-y0-y1-y2+max(div[1]['5'],div[2]['05']+y0,div[2]['15']+y1,div[2][l2+'5']+y2,div[3]['015']+y0+y1,div[3]['0'+l2+'5']+y0+y2,div[3]['1'+l2+'5']+y1+y2),1+deg-max(y0+y1+y2, div[1][l3], div[2]['0'+l3]+y0, div[2]['1'+l3]+y1, div[2]['2'+l3]+y2, div[3]['01'+l3]+y0+y1, div[3]['02'+l3]+y0+y2, div[3]['12'+l3]+y1+y2))
                        #upper3=min(max(elt[1]-sum(ys[i1] for i1 in elt[0]) for elt in new_conds[2]),1+deg-max(y0+y1+y2, div[1][l3], div[2]['0'+l3]+y0, div[2]['1'+l3]+y1, div[2]['2'+l3]+y2, div[3]['01'+l3]+y0+y1, div[3]['02'+l3]+y0+y2, div[3]['12'+l3]+y1+y2))
                        #lower3=max(lower3,max(conds_to_check[elt[0]+(2,)]-sum(ys[i1] for i1 in elt[0]) for elt in new_conds[2]))
                        #not useful because conds_to_check[5] is always 0
                    else:
                        upper3=lower3 #upper3=0
                    #upper3=min(-y0-y1-y2+max(div[1]['5'],div[2]['05']+y0,div[2]['15']+y1,div[2][l2+'5']+y2,div[3]['015']+y0+y1,div[3]['0'+l2+'5']+y0+y2,div[3]['1'+l2+'5']+y1+y2),1+deg-max(y0+y1+y2, div[1][l3], div[2]['0'+l3]+y0, div[2]['1'+l3]+y1, div[2]['2'+l3]+y2, div[3]['01'+l3]+y0+y1, div[3]['02'+l3]+y0+y2, div[3]['12'+l3]+y1+y2))
                else:####################################################################################
                    upper3=1+deg-max(y0+y1+y2, div[1][l3], div[2]['0'+l3]+y0, div[2]['1'+l3]+y1, div[2][l2+l3]+y2, div[3]['01'+l3]+y0+y1, div[3]['0'+l2+l3]+y0+y2, div[3]['1'+l2+l3]+y1+y2)
                
                if lower3<=1:
                    copy3_acoeffs=tuple((coeff for coeff in copy2_acoeffs if coeff[-1]))
                else:
                    copy3_acoeffs=tuple((coeff+(1,) for coeff in copy2_acoeffs if coeff[-1]))
                
                timedict['y2']+=time.time()-start2
                
                for y3 in range(lower3,upper3):
                    start3=time.time()
                    if add_condi1 and add_condi2:
                        if any((conds_to_check[elt[0]+(2,)]<=y3+sum(ys[i1] for i1 in elt[0])<elt[1] for elt in new_conds[2])):
                            if y3>1:
                                copy3_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[3]][y3],) for coeff in copy3_acoeffs if coeff[3]>=y3))
                                #copy3_acoeffs=tuple(((*coeff[:-1],coeff[-2]*binom_array[coeff[3]][y3]) for coeff in copy3_acoeffs if coeff[3]>=y3))
                                start4=time.time()
                                conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs if coeffi[-1]})
                                timedict['sum_cond']+=time.time()-start4
                            elif y3==1:
                                #copy3_acoeffs=tuple((coeff+(coeff[-1]*(coeff[3]%charac),) for coeff in copy3_acoeffs if coeff[3]))
                                copy3_acoeffs=tuple((coeff+(coeff[-1]*binom_array[coeff[3]][1],) for coeff in copy3_acoeffs if coeff[3]))#>=1))
                                #copy3_acoeffs=tuple(((*coeff,coeff[-1]*coeff[3]) for coeff in copy3_acoeffs if coeff[3]))
                                start4=time.time()
                                conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs if coeffi[-1]})
                                timedict['sum_cond']+=time.time()-start4
                            else:
                                start4=time.time()
                                conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs})
                                timedict['sum_cond']+=time.time()-start4
                            #n1+=1
                            if any((coeffi[-1] for coeffi in copy3_acoeffs)):
                                n1+=1
                        elif y3==1:
                            copy3_acoeffs=tuple((coeff+(1,) for coeff in copy3_acoeffs))
                            #print("y3=1 wasn't used for conds")
                        #else:
                        #    print(y3,"wasn't used for conds")
                    else:
                        if y3>1:
                            copy3_acoeffs=tuple((coeff[:-1]+(coeff[-2]*binom_array[coeff[3]][y3],) for coeff in copy3_acoeffs if coeff[3]>=y3))
                            #copy3_acoeffs=tuple(((*coeff[:-1],coeff[-2]*binom_array[coeff[3]][y3]) for coeff in copy3_acoeffs if coeff[3]>=y3))
                            start4=time.time()
                            conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs if coeffi[-1]})
                            timedict['sum_cond']+=time.time()-start4
                        elif y3==1:
                            #copy3_acoeffs=tuple((coeff+(coeff[-1]*(coeff[3]%charac),) for coeff in copy3_acoeffs if coeff[3]))
                            copy3_acoeffs=tuple((coeff+(coeff[-1]*binom_array[coeff[3]][1],) for coeff in copy3_acoeffs if coeff[3]))#>=1))
                            #copy3_acoeffs=tuple(((*coeff,coeff[-1]*coeff[3]) for coeff in copy3_acoeffs if coeff[3]))
                            start4=time.time()
                            conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs if coeffi[-1]})
                            timedict['sum_cond']+=time.time()-start4
                        else:
                            start4=time.time()
                            conditions.update({(n1,coeffi[4]):coeffi[-1] for coeffi in copy3_acoeffs})
                            timedict['sum_cond']+=time.time()-start4
                        #n1+=1
                        if any((coeffi[-1] for coeffi in copy3_acoeffs)):
                            n1+=1
                    timedict['y3']+=time.time()-start3   
    timedict['add_condssss']=timedict.get('add_condssss',0)+time.time()-start
    print('add_condsss took', time.time()-start,'seconds')
    return n1
#'''
    
def vecToPoly(vec,mon):
    global timedict
    #print(vec)
    #print(mon)
    start=time.time()
    #mon1=tuple((myARing(mon[place]) for place in range(len(mon))))
    ans=sum(map(mul,((coeff,myXRing.monomial(*(int(elt) for elt in mon[place][1:].split('b')))) for place,coeff in enumerate(vec))))
    #ans=sum(map(mul,((myARing(coeff),myRing.monomial(*(int(elt) for elt in coeff[1:].split('b')))) for coeff in acoeffs)))
    #ans=sum(map(mul,((coeff,myARing(mon[place])) for place,coeff in enumerate(vec))))
    #ans = myARing(0)
    #for place,coeff in enumerate(vec):
    #    #ans+=coeff*mon[place].coefficients()[0]
    #    #ans+=coeff*myARing(mon[place])
    #print(time.time()-start)
    #newAns=my_Duple(ans)
    timedict['poly']=timedict.get('poly',0)+time.time()-start
    #return newAns
    return ans


    
def multiply_div_class(div,multiplier):
    global timedict
    start=time.time()
    for key in div:
        if key=='d':
            div[key]*=multiplier
        else:
            for linspace in div[key]:
                div[key][linspace]*=multiplier
    timedict['multiply_div']=timedict.get('multiply_div',0)+time.time()-start

                
def minimize_para(exc,div,deg):
    global timedict
    start=time.time()
    if len(exc)==3:
        indices='012345'
        for chara in exc:
            indices=indices.replace(chara,'')
        ####deg_rigid=min(div[3][excpetional]-max(0,-deg+max(div[1][j]+div[2][exceptional.replace(j,'')] for j in exceptional),))
        #deg_rigid=div[3][exc]-max(0,-deg+max(div[1][exc[0]]+div[2][exc[1:]],div[1][exc[2]]+div[2][exc[:-1]],div[1][exc[1]]+div[2][exc[0::2]]),-2*deg+sum(div[1][indi] for indi in exc)+div[3][indices],(-deg+div[2][exc[1:]]+div[2][exc[:-1]]+div[2][exc[0::2]]+div[3][indices])/2)
        #switched so that always an integer: if it was 1.5, now is 1.  i.e., is floor.  This changes no calcs, even bounds (Still want div>= div-minval)
        deg_rigid=div[3][exc]-max(0,-deg+max(div[1][exc[0]]+div[2][exc[1:]],div[1][exc[2]]+div[2][exc[:-1]],div[1][exc[1]]+div[2][exc[0::2]]),-2*deg+sum(div[1][indi] for indi in exc)+div[3][indices],(-deg+div[2][exc[1:]]+div[2][exc[:-1]]+div[2][exc[0::2]]+div[3][indices])//2)
        timedict['min_planes']=timedict.get('min_planes',0)+time.time()-start
        return deg_rigid
    elif len(exc)==2:
        deg_rigid=div[2][exc]-max(0,-deg+div[1][exc[0]]+div[1][exc[1]])
        timedict['min_lines']=timedict.get('min_lines',0)+time.time()-start
        return deg_rigid
        

timedict=dict() 
    
def main_div(str_input,multiplier=1,base_fld=QQ,symmetry=True):
    global timedict
    #global myRing
    #global myARing
    #global myStackedRing
    global myXRing
    #global x0,x1,x2,x3,x4
    #global stack_map
    start=time.time()
    
    #str_input=''
    print('\n\n',str_input)
    
    #make divisor
    if symmetry==True:
        vect1,acted_on_div=find_S7_rep(convert_to_vect(str_input),'div')
    else:
        vect1=convert_to_vect(str_input)
        acted_on_div=tuple((str(i) for i in range(7)))
    div=convert_to_dict(vect1)
    multiply_div_class(div,multiplier)
    #div[3]['045']-=1
    #div[3]['145']-=1
    #use knowledge from Losev-Manin space to construct relevant rings
    acoeffs=construct_monomial_coeffs(div)
    xs=list('x%i' % i for i in range(0,5))
    #myARing=PolynomialRing(base_fld,acoeffs)
    #myRing=PolynomialRing(myARing,xs)
    myXRing=PolynomialRing(base_fld,xs)
    del xs #should I do this????
    print("finished building rings and maps")
    
    #now, find linear series using whatever method is implemented
    #f=construct_generic_polynomial(acoeffs)
    #conditions=[]
    #conditions=Sequence([],universe=myARing,check=False,immutable=False)
    deg=div['d']
    
    
    #Temporary experiment
    #conditions1=Sequence([],universe=myARing,check=False,immutable=False)
    charac=base_fld.characteristic()
    matrix_dict=dict()
    if charac==0:
        n1=add_conds1(deg,div,matrix_dict,acoeffs,4,0)
    else:
        n1=add_conds2(deg,div,matrix_dict,acoeffs,4,0,charac)
    
    if max(minimize_para(exc,div,deg) for exc in ('45','045','145','245'))>=1:
        #Temp experiment
        if charac==0:
            n1=add_conds1(deg,div,matrix_dict,acoeffs,3,n1)
        else:
            n1=add_conds2(deg,div,matrix_dict,acoeffs,3,n1,charac)
        
    if minimize_para('345',div,deg)>=1:
        #Temp experiment
        if charac==0:
            n1=add_conds1(deg,div,matrix_dict,acoeffs,2,n1)
        else:
            n1=add_conds2(deg,div,matrix_dict,acoeffs,2,n1,charac)
        
    print("The number of conditions is",n1,"with",len(matrix_dict),"nonzero entries")
    start2=time.time()
    start1=time.time()
    #M1=matrix(base_fld,n1,len(acoeffs),matrix_dict,immutable=True,sparse=False)
    M1=matrix(base_fld,matrix_dict,immutable=True,sparse=False)
    timedict['make_matrix']=timedict.get('make_matrix',0)+time.time()-start1
    print('making matrix took',time.time()-start1)
    start1=time.time()
    C=M1.right_kernel()
    timedict['find kernel']=timedict.get('find kernel',0)+time.time()-start1
    start1=time.time()
    dim=C.dimension()
    timedict['kernel dimension']=timedict.get('kernel dimension',0)+time.time()-start1
    print(dim,'is dimension, took', time.time()-start2)
    
    #if dim !=1:
    if dim==0:
        poly=0
    else:
        start1=time.time()
        ansVec=C.basis()[0]
        timedict['basis_vect']=timedict.get('basis_vect',0)+time.time()-start1
        poly=vecToPoly(ansVec,acoeffs)
    
    if poly !=0:
        start1=time.time()
        poly=factorize1(poly,2)
        print ("The divisor class factored with singular 2 is ", poly, 'took', time.time()-start1)
        timedict['factorize']=timedict.get('factorize',0)+time.time()-start1
    print("The dimension of the linear series is ", dim)
    if dim==1:
        #print "The linear series is spanned by ", poly
        print(div)
    timedict['main']=timedict.get('main',0)+time.time()-start
    for pair in timedict.items():
        print(pair)
    print(div)
    return dim,poly,acted_on_div


#SECTION FOR CURVES:::::::::::::::::::::::::::::::::::::::::::::::::::::::

def convert_to_list(vect2):
    counter=0
    curve=list()
    curve.append(tuple(('l',vect2[counter])))
    counter+=1
    for i in range(0,6):
        if vect2[counter]!=0:
            curve.append(tuple((str(i),vect2[counter])))
        counter+=1
    for i in range(0,6):
        for j in range(i+1,6):
            if vect2[counter]!=0:
                curve.append(tuple((str(i)+str(j),vect2[counter])))
            counter+=1
    for i in range(0,6):
        for j in range(i+1,6):
            for k in range(j+1,6):
                if vect2[counter]!=0:
                    curve.append(tuple((str(i)+str(j)+str(k),vect2[counter])))
                counter+=1
    return curve

def sep_curve(curve):
    mon_conds=list()
    p5_conds=list()
    for cond in curve[1:]:
        if '5' in cond[0]:
            p5_conds.append(cond)
        else:
            mon_conds.append(cond)
    return mon_conds,p5_conds

def find_pt_on_div(base_fld,div,check_jacobian):
    base=div.parent().base_ring()
    if base==QQ:
        div=div.numerator() #or div=div.change_ring(ZZ) and make sure content (gcd of coefficients) is 0
        if div.content() !=1:
            div=(div/(div.content()))
            if div.parent().base_ring()==QQ:
                div=div.numerator()
            if div.content() !=1:
                print("content of div is not 1.  Need to use something different than numerator")
        while len(factorize1(div.change_ring(base_fld),1))>1:
            base_fld=GF(next_prime(base_fld.characteristic()+1))
        #Should be good after this?  return base_fld (remember to return base_fld)
        div1=div.change_ring(base_fld)
    else:
        #div1=div
        if div.parent().base_ring().characteristic() != base_fld.characteristic():
            print('characteristic of base_fld and divisor didn\'t match up')
            base_fld=div.parent().base_ring()
        div1=div.change_ring(base_fld)
    
    #Now, pretend that have checked that div is irreducible over base_fld (use factor from singular), changed characteristic if not to next prime (next prime? there is a sage function), and returned new base_fld
    #print("Still need to check if div is irred. over base_fld, and, if not, change to next prime.  Should be doable.  Maybe, before construct div, use an integer vector, so that get a poly over integers.  Easier?")
    xs=div1.variables() #or div.parent().gens()
    #sub_dict={xs[-1]:1}
    #for vari in xs[:-3]:
    div1=div1.specialization({xs[0]:1})
    xs=div1.variables()
    
    jacobian_div1=PolynomialSequence((div1.derivative(u) for u in xs),div1.parent())
    singular_jacobian=PolynomialSequence((div1.parent()(0) for u in xs),div1.parent())
    
    powr=ZZ.random_element()
    while gcd(powr,(base_fld.cardinality()-1))>1: #powr % (base_fld.cardinality()-1)==0:
        powr=ZZ.random_element()
    
    u=base_fld.multiplicative_generator()**(powr) #or .primitive_element()
    found_rational_pt=False
    while not found_rational_pt:
        x1=u
        while x1 !=1:
            #div2=div1(x1,xs[1],xs[2],xs[3])
            div2=div1.subs({xs[0]:x1})
            print(div2.parent())
            jacobian_div2=jacobian_div1.subs({xs[0]:x1})
            x2=u
            while x2!= 1:
                if x2==x1:
                    x2*=u
                else:
                    #div3=div2(x2,xs[2],xs[3])
                    print(div2.parent())
                    print(xs[1],xs[1].parent())
                    div3=div2.subs({xs[1]:x2})
                    jacobian_div3=jacobian_div2.subs({xs[1]:x2})
                    x3=u
                    while x3 !=1:
                        if x3==x2 or x3==x1:
                            x3*=u
                        else:
                            #div4=div1(x3,xs[3])
                            div4=div3.subs({xs[2]:x3})
                            jacobian_div4=jacobian_div3.subs({xs[2]:x3})
                            x4=u
                            while x4 !=1: #could use factorize(,1) instead to find roots of the polynomial, if they exist.  Might be faster, if this is slow.  Check later.  Actually should be much faster
                                #also roots(), any_root() from univariate polynomial base class in sage 9.2
                                """
                                Idea of any_root(): just use specialize instead of subs (probs need to change xs too so that get right variable rings), then use div4.any_root() (if its none, and doesnt match values of xs, great!)
                                Idea of roots(): same as any_root(), but use div4.roots(multiplicities=False, algorithm=?None?), then returns a list of roots, check if any are nondegenerate/not on exceptionals
                                Idea of factorize(,1) instead:
                                basically the same as above, use factorize(div4,1) to get a list of factors, then check each factor
                                if factor.degree()==1: then check if factor (root) is nondegenerate (doesn't lie on exceptional): -factor.constant_coefficient()=root, see if root is distinct from 1,x1,x2,x3,x4 (same criteria applies above)
                                #"""
                                if x4==x3 or x4==x2 or x4==x1:
                                    x4*=u
                                else:
                                    if not check_jacobian:
                                        return base_fld,list((base_fld(1),x1,x2,x3,x4))
                                    elif div4.subs({xs[3]:x4})==0 and jacobian_div4.subs({xs[3]:x4})!=singular_jacobian: #base_fld(0) #might wanna store base_fld(0) first
                                        print(jacobian_div4.subs({xs[3]:x4}),'is the jacobian')
                                        return base_fld,list((base_fld(1),x1,x2,x3,x4))
                                    else:
                                        x4*=u
                            x3*=u
                    x2*=u
            x1*=u
        
        #when have checked every element in ground field.
        if base==QQ:
            base_fld=GF(next_prime(base_fld.characteristic()+1))
            while len(factorize1(div.change_ring(base_fld),1))>1:
                base_fld=GF(next_prime(base_fld.characteristic()+1))
            div1=div.change_ring(base_fld)
        else:
            base_fld=GF((base_fld.cardinality())*base_fld.characteristic())
        xs=div1.variables() #or div.parent().gens()
        div1=div1.specialization({xs[0]:1})
        xs=div1.variables()
        u=base_fld.multiplicative_generator() #or .primitive_element()
        if base_fld.cardinality()>2**16:
            print("base field has extremely large cardinality >2^16 should stop computation")
            
            
            
            
def S7_acts_on_P4(acted_on_curve,acted_on_div,pt_in_P4):
    #How does S7 act on P4?
    #Well, letting p0,p1,...,p4 be the points [1,0,0,0,0],[0,1,0,0,0],...,[0,0,0,0,1]
    #p5 be the point [1,1,1,1,1]
    #Then S6 < S7 acts on P4 via the PGL element which permutes the corresponding points
    #But, S7 only acts on the open locus of P4 that we'e guaranteed the pt_on_orig_div lies in
    #element i6 in S7 acts by what?  fixes Ei, Eij, Eijk.  Sends Hjklm to En, sends .... interchanges planes and lines
    #lets looks at 56.  Right.  Its a map to P4, and degree 4 (! rational cant say that), so find line bundle and 5 sections
    #try x1x2x3x4, x0x2x3x4, x0x1x3x4, x0x1x2x4, x0x1x2x3
    #Yes, 56 is (x0,x1,x2,x3,x4)--------->(x1x2x3x4, x0x2x3x4, x0x1x3x4, x0x1x2x4, x0x1x2x3)
    #Or, equiv, (x0,x1,x2,x3,x4)--------->(1/x0, 1/x1, 1/x2, 1/x3, 1/x4) #This description works on the open locus where none are 0
    #So, to get entire action of S7, suffices to have action of 56 and the permutations from everything else.
    
    #need to act by inverse of acted_on_div first, then by acted_on_curve
    perm=dict()
    for i,image in enumerate(acted_on_div):
        perm[image]=acted_on_curve[i]
    #This has now produced (as perm) acted_on_curve*(acted_on_div)^{-1}
    if perm['6']!='6':
        if perm['5']!='6':
            for key,value in perm.items():
                if value=='6':
                    change_to_5=key
            #5---perm(change to 5)
            #change to 5-----perm(5)
            sent_5_to=perm['5']
            perm['5']=perm[change_to_5] #will be 6
            perm[change_to_5]=sent_5_to
            #this acts by transposition change_to_5, '5', and need to change pt_in_P4
            #on algebra, if xi=coord of change_to_5, then sends xi--->xi, and xj-----> xi-xj
            #Since this transposition sends, if xi=coord of change_to_5, (a,b,c,d,e)-----> (xi-a,xi-b,....,xi,...,xi-e)
            image=int(change_to_5)
            xi=pt_in_P4[image]
            for i in range(5):
                if i != image:
                    pt_in_P4[i]=xi-pt_in_P4[i]
        #Then, act by 56:
        for i in range(5):
            pt_in_P4[i]=1/pt_in_P4[i]
        perm['5']=perm['6']
        perm['6']='6'
        #dont need that last line technically, just for math rigor, but i don't use it
    if perm['5']!='5':
        for key, value in perm.items():
            if value=='5':
                change_to_5=key
        sent_5_to=perm['5']
        perm['5']=perm[change_to_5] #will be 5
        perm[change_to_5]=sent_5_to
        #this acts by transposition change_to_5, '5', and need to change pt_in_P4
        #on algebra, if xi=coord of change_to_5, then sends xi--->xi, and xj-----> xi-xj
        #Since this transposition sends, if xi=coord of change_to_5, (a,b,c,d,e)-----> (xi-a,xi-b,....,xi,...,xi-e)
        image=int(change_to_5)
        xi=pt_in_P4[image]
        for i in range(5):
            if i != image:
                pt_in_P4[i]=xi-pt_in_P4[i]
    
    #Now, just act by the obvious symmetry
    perm1={perm[str(i)]:str(i) for i in range(5)}
    perm=perm1 #This is necessary to get the correct action.
    new_pt=list((pt_in_P4[int(perm[str(i)])] for i in range(5)))
    
    return new_pt
    
        

def make_acoeffs(div,cond,base_fld,acted_on_div,acted_on_curve): #technically checking for the Error is not needed
    check_jacobian=True
    if div==1:
        xs=list('x%i' % i for i in range(0,5))
        myXRing=PolynomialRing(QQ,xs)
        x0,x1,x2,x3,x4 = myXRing.gens()
        div=myXRing(x0**2*x1**3*x2 + x0**2*x1**3*x3 + x0*x1**2*x2**2*x4 + x0*x1**2*x2*x3*x4 + x0*x1*x2*x3**2*x4 + x0*x2**2*x3**2*x4 + x1*x3**3*x4**2 + x2*x3**3*x4**2)
        check_jacobian=False
    if div:
        base_fld,pt_on_orig_div=find_pt_on_div(base_fld,div,check_jacobian)
        pt_on_div=S7_acts_on_P4(acted_on_curve,acted_on_div,pt_on_orig_div)
        return pt_on_div,list(),base_fld
    
    #this code can be simplified (but it doesn't make much difference time-wise)
    if cond[1]<=0:
        print("Error, p5 cond is zero")
    acoeffs=list()
    free_acoeffs=list()
    for i in range(0,5):
        if str(i) in cond[0]:
            acoeffs.append('a'+str(i))
            free_acoeffs.append('a'+str(i))
        else:
            acoeffs.append(1)
    return acoeffs,free_acoeffs,base_fld
    

def make_roots(deg,mon_conds):
    roots=list()
    counter=0
    for cond in mon_conds:
        temp_indices='01234'
        for letter in cond[0]:
            temp_indices=temp_indices.replace(letter,'')
        for i in range(0,cond[1]):
            roots.append('y'+temp_indices+'b'+str(i))
        counter+=cond[1]*len(temp_indices)
    for i in range(0,5*deg-counter):
        roots.append('r'+str(i))
    
    return roots
    

def make_p5_pts(p5_conds):
    p5_pts=list()
    for cond in p5_conds:
        temp_indices='01234'
        for letter in cond[0][:-1]:
            temp_indices=temp_indices.replace(letter,'')
        for i in range(0,cond[1]):
            p5_pts.append('z'+temp_indices+'b'+str(i))
    #want to make first p5 point to be s=0, rather than a variable, and use this to limit the number of ai's needed.
    return p5_pts

def make_Fs(deg,mon_conds,roots,acoeffs):  #maybe clean this up a little
    faux_Fs=list((list() for i in range(0,5))) #list of roots that each F has, expressed as (t-(root)s)
    for cond in mon_conds:
        indices='01234'
        for letter in cond[0]:
            indices=indices.replace(letter,'')
        for letter in indices:
            for i in range(0,cond[1]):
                faux_Fs[int(letter)].append(myRing('y'+indices+'b'+str(i)))
    counter=0
    for polyF in faux_Fs:
        l=len(polyF)
        if l<deg:
            for i in range(l,deg):
                polyF.append(myRing('r'+str(counter)))
                counter+=1
    
    real_Fs=list()
    for i, polyF in enumerate(faux_Fs):
        placeholder=myRing(acoeffs[i])
        for root in polyF:
            placeholder*=(myRing('t')-root)
        real_Fs.append(placeholder)
    
    return faux_Fs,real_Fs



def add_conds(ideal_gens,i,j,faux_Fs,acoeffs,p5_conds,div):
    #adds constraints from fi-fj
    #make h, g, divide g by h, and let remainder = 0
    
    #make h:
    h=myRing(1)
    #first do first cond
    cond=p5_conds[0]
    if str(i) not in cond[0]:
        if str(j) not in cond[0]:
            #h*=myRing('t')
            #h*=myRing(1) #multiplying by t was wrong.  We basically omit the first condition, because it happens at s=0, and is recorded in the equality of acoeffs (which we also dehomogenize)
            if not div:
                lower=1
            else:
                lower=0
            if cond[1]>lower:#1:
                indices='01234'
                for letter in cond[0][:-1]:
                    indices=indices.replace(letter,'')
                #for k in range(1,cond[1]):
                for k in range(lower,cond[1]):
                    h*=(myRing('t')-myRing('z'+indices+'b'+str(k)))
    
    #then do rest of conds
    for cond in p5_conds[1:]:
        if str(i) not in cond[0]:
            if str(j) not in cond[0]:
                indices='01234'
                for letter in cond[0][:-1]:
                    indices=indices.replace(letter,'')
                for k in range(0,cond[1]):
                    h*=(myRing('t')-myRing('z'+indices+'b'+str(k)))
    
    #then construct g
    p1=faux_Fs[i][:]
    p2=faux_Fs[j][:]
    shared=list()
    for root in p1:
        if root in p2:
            shared.append(root)
    for root in shared:
        p1.remove(root)
        p2.remove(root)
    g1=myRing(acoeffs[i])
    g2=myRing(acoeffs[j])
    for root in p1:
        g1*=(myRing('t')-root)
    for root in p2:
        g2*=(myRing('t')-root)
    g=g1-g2
    
    #then, reduce g by h
    #print g
    #print h
    polyn=g.reduce((h,))  #COULD THINK ABOUT DOING THIS FOR A SINGLE ROOT AT A TIME, SINCE LOCALIZE AWAY FROM BAD LOCUS
    #print polyn
    polyno=polyn.polynomial(myRing('t'))
    
    #finally:
    ideal_gens.extend(polyno.coefficients())
    
    #TO CHANGE TO TAKING REMAINDER BY ONE THING AT A TIME, TRY THE FOLLOWING:
    #Still construct g in the same manner, but just iterate over p5 conditions, and select appropriate number of g to reduce
    #for instance, if its a plane, use only 2 g's, if its a line, use 3, f1-f2, f2-f3, f3-f4, but don't use the others
    #this could reduce the number of conditions we impose
    #the fact that use g, rather than fi-fj, actually doesn't matter.  It just lowers the degree of the generator, which is good
    #since use g, the difference will be dividing the remainder by z123-y123, for example.
    



def fix_auto_P1(ideal_gens,div,p5_pts,my_Ring,base_fld):
    fixed_vars={'marked_pts':dict(),'r_dict':dict()}
    sub_dict=dict()
    
    ##Part where set up substitution and where build fixed_vars.  Could port over the build fixed_vars to another function, perhaps, cause will use later
    if div and len(p5_pts)>1:
        #if len(p5_pts)>1:
        #    #sub_dict[my_Ring(p5_pts[0])]=my_Ring(0)
        #    #sub_dict[my_Ring(p5_pts[1])]=my_Ring(1)
        for i1 in range(2):
            sub_dict[my_Ring(p5_pts[i1])]=my_Ring(i1)
            indices='012345'
            for letter in p5_pts[i1].split('b')[0][1:]:
                indices=indices.replace(letter,'')
            fixed_vars['marked_pts'][base_fld(i1)]=indices
    elif len(p5_pts)>2:
        for i1 in range(2):
            sub_dict[my_Ring(p5_pts[i1+1])]=my_Ring(i1)
            indices='012345'
            for letter in p5_pts[i1+1].split('b')[0][1:]:
                indices=indices.replace(letter,'')
            fixed_vars['marked_pts'][base_fld(i1)]=indices
    else:
        #sub_dict[my_Ring.gens()[-1]]=my_Ring(0)
        #sub_dict[my_Ring.gens()[-2]]=my_Ring(1)
        for i1 in range(2):
            sub_dict[my_Ring.gens()[-i1-1]]=my_Ring(i1)
            str_var=my_Ring.gens()[-i1-1].univariate_polynomial().parent().variable_names_recursive()[0]
            if 'z' in str_var:
                indices='012345'
                for letter in str_var.split('b')[0][1:]:
                    indices=indices.replace(letter,'')
                fixed_vars['marked_pts'][base_fld(i1)]=indices
            elif 'y' in str_var:
                indices='01234'
                for letter in str_var.split('b')[0][1:]:
                    indices=indices.replace(letter,'')
                fixed_vars['marked_pts'][base_fld(i1)]=indices
            elif 'r' in str_var:
                fixed_vars['r_dict'][str_var]=base_fld(i1)
            else:
                print("ERROR, not enough variables in ring.  Needed to fix an a_var.  This implies too few dimensions for curve")
    ideal_gens2=Sequence((i1.specialization(sub_dict) for i1 in ideal_gens))#,ideal_gens[0].specialization(sub_dict).parent())
    return ideal_gens2,fixed_vars,list(ideal_gens2.ring().gens())



def random_subscheme(ideal_gens,free_gens,extra_dim,base_fld):
    sub_dict=dict()
    prev_values=list((base_fld(0),base_fld(1)))
    print(extra_dim)
    extra_dim=max(0,extra_dim)
    print(free_gens)
    rand_fix=random.sample(free_gens, extra_dim)
    for elt in range(0,extra_dim):
        new_Hplane=base_fld.random_element()
        #new_Hplane=base_fld(ZZ.random_element())
        #str_var=rand_fix[elt].univariate_polynomial().parent().variable_names_recursive()[0]
        #if 'a' in str_var:
        if 'a' in rand_fix[elt].univariate_polynomial().parent().variable_names_recursive()[0]:
            while new_Hplane in prev_values[:2]:
                new_Hplane=base_fld.random_element()
                #new_Hplane=base_fld(ZZ.random_element())
        else:
            while new_Hplane in prev_values:
                new_Hplane=base_fld.random_element()
                #new_Hplane=base_fld(ZZ.random_element())
            prev_values.append(new_Hplane)
        sub_dict[rand_fix[elt]]=new_Hplane
    ideal_gens2=Sequence((elt.specialization(sub_dict) for elt in ideal_gens))#,ideal_gens[0].specialization(sub_dict).parent())
    free_gens=list(ideal_gens2.ring().gens())
    #free_gens=list((valu.univariate_polynomial.parent.variable_names_recursive()[0] for valu in ideal_gens2.ring().gens()))
    
    large_list=list()
    for i1,elt in enumerate(free_gens):
        #str_var=elt.univariate_polynomial().parent().variable_names_recursive()[0]
        #if 'a' in str_var:
        if 'a' in elt.univariate_polynomial().parent().variable_names_recursive()[0]:
            for valu in prev_values[:2]:
                large_list.append(elt-valu)
                #ideal_gens2.append(elt-valu)
        else:
            for valu in prev_values:
                large_list.append(elt-valu)
                #ideal_gens2.append(elt-valu)
            #for elt2 in (valu for valu in free_gens[i1+1:] if 'a' not in valu.univariate_polynomial().parent().variable_names_recursive()[0]):
            for elt2 in free_gens[i1+1:]:
                large_list.append(elt-elt2)
                #ideal_gens2.append(elt-elt2)
        
    
    ideal_gens=groebner1(ideal_gens2)
    ideal_candids=facstd1(ideal_gens,ideal(large_list)) #sometimes get stuck here.   idk why.  maybe compute groebner beforehand?
    ideal_candids2=list()
    dim0_nondegen=False
    for elt in ideal_candids:
        if not dim0_nondegen:
            elt2=groebner1(interred1(elt))
            #extra_dim=dim1(elt2)
            extra_dim=ideal(elt2).dimension()
            if extra_dim>=0:
                dim0_nondegen=True
                ideal_candids2.append(elt2)
        else:
            ideal_candids2.append(elt)
    if dim0_nondegen:
        return dim0_nondegen,list((ideal_candids2,free_gens,sub_dict,large_list,extra_dim,prev_values))
    else:
        return dim0_nondegen,None
    
def random_localization(extra_dim,orig_gens,free_gens,large_list,base_fld,prev_values):
    large_list=large_list[:]
    
    temp_dim=extra_dim
    inverted=1
    #orig_gens=?????
    localize_away=list()
    my_intermediate_ring=PolynomialRing(base_fld,('t',)+orig_gens.ring().variable_names_recursive())
    while extra_dim >0:
        while temp_dim !=0:  #Could put this part into a dif function altogether with random_subschemes part in there too
            rand_fix=random.sample(free_gens,extra_dim)
            temp_gens=list() #Sequence??? if undefined addition
            #temp_gens=dict()
            temp_vals=list()
            for elt in range(0,extra_dim):
                new_Hplane=base_fld.random_element()
                #new_Hplane=base_fld(ZZ.random_element())
                #'''
                #str_var=rand_fix[elt].univariate_polynomial().parent().variable_names_recursive()[0]
                #if 'a' in str_var:
                if 'a' in rand_fix[elt].univariate_polynomial().parent().variable_names_recursive()[0]: #perhaps don't actually want to do this.  These aren't constraints that I actually add, so it doesn't matter if they're degenerate
                    while new_Hplane in prev_values[:2]:
                        new_Hplane=base_fld.random_element()
                        #new_Hplane=base_fld(ZZ.random_element())
                else:
                    while new_Hplane in prev_values or new_Hplane in temp_vals: #again, perhaps this isn't something I want to do. Its probably okay if new_Hplane is the same as a previous value.
                        new_Hplane=base_fld.random_element()
                        #new_Hplane=base_fld(ZZ.random_element())
                    temp_vals.append(new_Hplane)
                #''' #if want to not limit new_Hplane to new values, get rid of first #
                temp_gens.append(rand_fix[elt]-new_Hplane)
                #temp_gens[rand_fix[elt]]=new_Hplane
            #temp_ideal=Sequence((elt.specialization(temp_gens) for elt in orig_gens))#,orig_gens[0].specialization(temp_gens).parent())
            #This ends the part that is similar to the random subscheme part.  
            
            temp_ideal=Sequence(orig_gens+tuple(temp_gens))
            #temp_dim=dim1(groebner1(interred1(temp_ideal)))
            #temp_dim=dim1(groebner1(interred1(facstd1(interred1(temp_ideal))[0]))) #would need to change to get all facstd1's parts
            temp_ideal=groebner1(interred1(temp_ideal))
            temp_dim=ideal(temp_ideal).dimension()
        temp_pts=ideal(temp_ideal).minimal_associated_primes()
        while len(temp_pts)>0:
            temp_dict=dict()
            for elt in large_list: #could be improved to be more efficient. For instance, only construct sets once, and then remove elts from them.
                temp_dict[elt]=set()
                for pt in temp_pts:
                    if elt in pt:
                        temp_dict[elt].add(pt)
            if len(temp_dict)==0:
                print('temp_dict is empty!  Could break loop here, kinda do that anyway')
            val_max=0
            for key,value in temp_dict.items():
                if len(value)>val_max:
                    invert=key
                    val_max=len(value)
            if val_max==0:
                print(temp_pts)
                print("DID NOT HAVE EXPECTED DIMENSION OF NONDEGENERATE LOCUS!!!!!!!!")
                orig_gens=temp_ideal
                break
            large_list.remove(invert)
            for pt in temp_dict[invert]:
                temp_pts.remove(pt)
            inverted*=invert
            localize_away.append(invert) #might want to think about just using inverted, rather than many diff elts to invert
        new_gens=(inverted*my_intermediate_ring('t')-1,)+tuple(orig_gens)
        #could do some stuff with groebner bases here.  IDK not optimized yet.  Like process new_gens more
        dim0_ideal=my_intermediate_ring.ideal(new_gens)
        #extra_dim=dim1(dim0_ideal)
        extra_dim=dim0_ideal.dimension()
        print("new extra_dim is", extra_dim)
        temp_dim=extra_dim
    
    if extra_dim!=0:
        return False,None
    
    new_vars=list()
    for elt in range(0,len(localize_away)):
        new_vars.append('t'+str(elt))
    myLocRing=PolynomialRing(base_fld,orig_gens.ring().variable_names_recursive()+tuple(new_vars)) #consider switching order
    loc_gens=list(orig_gens)
    for i1,elt in enumerate(localize_away):
        loc_gens.append(myLocRing('t'+str(i1))*elt-1)
    dim0_ideal=myLocRing.ideal(loc_gens)
    
    #dim0_ideal=ideal(groebner1(interred1(dim0_ideal)))
    dim0_nondegen=False
    pt_candids2=list()
    for elt in facstd1(interred1(dim0_ideal),myLocRing.ideal(large_list)):
        if not dim0_nondegen:
            pt_candidates=ideal(groebner1(interred1(elt))).minimal_associated_primes()
            if pt_candidates:
                dim0_nondegen=True
                pt_candids2.append(pt_candidates)
        else:
            pt_candids2.append(elt)
    if dim0_nondegen:
        #return dim0_nondegen,list((myLocRing,pt_candids2,large_list))
        return dim0_nondegen,list((myLocRing,pt_candids2))
    else:
        return dim0_nondegen,None


def find_nondegen_pts(pt_candidates,large_list):
    nondegen_pts=list()
    for component in pt_candidates:
        non_degenerate=True
        if set(component.gens()).intersection(set(large_list)): #The empty set is false--all other sets are true
            non_degenerate=False
            #print("This minimal prime had an easy elimination")
        if non_degenerate:
            #start1=time.time()
            for degen_elt in large_list:
                if degen_elt in component:
                    non_degenerate=False
                    #print("This minimal prime was actually degenerate")
                    break
            #print("It took", time.time()-start1, "seconds to show that this minimal prime wasn't degenerate\n")
        if non_degenerate:
            nondegen_pts.append(component)
    return nondegen_pts


def random_process(ideal_gens,free_gens,extra_dim,base_fld,fixed_vars):
    dim0_nondegen=False
    count=0
    while not dim0_nondegen:
        dim0_nondegen,data=random_subscheme(ideal_gens,free_gens,extra_dim,base_fld)
        if not dim0_nondegen:
            print("random_subscheme failed to find points.  Trying again.")
            count+=1
            if count>1:
                return dim0_nondegen,None
    ideal_candids,free_gens,sub_dict,large_list,extra_dim,prev_values=data
    dim0_nondegen=False
    for i1,elt in enumerate(ideal_candids):
        if not dim0_nondegen:
            if i1==0:
                dim0_nondegen,data=random_localization(extra_dim,elt,free_gens,large_list,base_fld,prev_values)
            else:
                elt2=groebner1(interred1(elt))
                #extra_dim=dim1(elt2)
                extra_dim=ideal(elt2).dimension()
                if extra_dim>=0:
                    dim0_nondegen,data=random_localization(extra_dim,elt2,free_gens,large_list,base_fld,prev_values)
            if dim0_nondegen:
                myLocRing,pt_candids_list=data
                #myLocRing,pt_candids_list,large_list=*data
                for i2,elt2 in enumerate(pt_candids_list):
                    if i2==0:
                        nondegen_pts=find_nondegen_pts(elt2,large_list)
                    elif not dim0_nondegen:
                        pt_candidates=ideal(groebner1(interred1(elt2))).minimal_associated_primes()
                        nondegen_pts=find_nondegen_pts(pt_candidates,large_list)
                    if not nondegen_pts:
                        dim0_nondegen=False
        #elif "min dim of nondegen_pts too high": dim0_nondegen=False
    if dim0_nondegen:
        #this part, where change fixed_vars, could be put in another function, because appears here and 2 other places with some similarity
        for monom,valu in sub_dict.items():
            str_var=monom.univariate_polynomial().parent().variable_names_recursive()[0]
            if 'z' in str_var:
                indices='012345'
                for letter in str_var.split('b')[0][1:]:
                    indices=indices.replace(letter,'')
                fixed_vars['marked_pts'][valu]=indices
            elif 'y' in str_var:
                indices='01234'
                for letter in str_var.split('b')[0][1:]:
                    indices=indices.replace(letter,'')
                fixed_vars['marked_pts'][valu]=indices
            elif 'r' in str_var:
                fixed_vars['r_dict'][str_var]=valu
            elif 'a' in str_var:
                fixed_vars[str_var]=valu
            else:
                print("Error.  Unexpected Ring Variable fixed in sub_dict from random_subscheme")
        
        #return dim0_nondegen,list((myLocRing,nondegen_pts,free_gens))
        return dim0_nondegen,list((myLocRing,nondegen_pts))
    else:
        return dim0_nondegen,None


def pick_lowDeg_nondegen_pt(nondegen_pts):
    #could use singular's vdim instead for this, which might be better.
    chosen=nondegen_pts[0]
    min_deg=chosen.vector_space_dimension()
    if len(nondegen_pts)>1:
        for point in nondegen_pts[1:]:
            if point.vector_space_dimension()<min_deg:
                chosen=point
                min_deg=point.vector_space_dimension()
    #chosen=ideal(groebner1(interred1(chosen)))
    return chosen,min_deg

def find_galois_representative(chosen,min_deg,myLocRing,base_fld_order):
    chosen=ideal(groebner1(interred1(chosen)))
    print(base_fld_order)
    print(min_deg)
    print(base_fld_order**min_deg)
    new_ideal=chosen.change_ring(myLocRing.change_ring(GF(base_fld_order**min_deg)))
    chosen1=ideal(groebner1(interred1(facstd1(new_ideal)[0])))
    if chosen1.vector_space_dimension()==1:
        print('facstd was useful in finding galois representative, split entirely')
        if new_ideal.vector_space_dimension()==1:
            print('actually, it was just a single point to begin with')
        return chosen1.gens()
    elif chosen1.vector_space_dimension()<new_ideal.vector_space_dimension():
        print('facstd was useful in finding galois representative, didnt split entirely')
        new_pts=chosen1.minimal_associated_primes()
        final_pt=groebner1(interred1(new_pts[0]))#.groebner_basis()
        return final_pt
    else:
        print('facstd was not useful in finding galois representative')
        new_pts=new_ideal.minimal_associated_primes()
        final_pt=groebner1(interred1(new_pts[0]))#.groebner_basis()
        return final_pt


def construct_curve_eqs(my_PID,t,fixed_vars,final_pt,curve_deg,acoeffs,div):
    defining_equations=list((my_PID(1) for i in range(0,5)))  #Edit to include what happens if div is not False
    if div:
        defining_equations=list((my_PID(valu) for valu in acoeffs))
        #print("DO SOMETHING WITH Acoeffs returned from divisor")
    
    for key,valu in fixed_vars.items():
        if key=='marked_pts':
            for key1,valu1 in valu.items():
                if '5' not in valu1:
                    indices='01234'
                    for letter in valu1:
                        indices=indices.replace(letter,'')
                    for letter in indices:
                        defining_equations[int(letter)]*=(t-key1)
        elif 'a' in key:
            defining_equations[int(key[1])]*=valu
        
    #consider writing a separate function??????
    for elt in final_pt:
        str_var=elt.univariate_polynomial().parent().variable_names_recursive()[0]
        pt_value=-elt.constant_coefficient()
        if 'r' in str_var:
            fixed_vars['r_dict'][str_var]=pt_value
        elif 'z' in str_var:
            indices='012345'
            for letter in str_var.split('b')[0][1:]:
                indices=indices.replace(letter,'')
            fixed_vars['marked_pts'][pt_value]=indices
        elif 'y' in str_var:
            indices='01234'
            for letter in str_var.split('b')[0][1:]:
                indices=indices.replace(letter,'')
                defining_equations[int(letter)]*=(t-pt_value)
            fixed_vars['marked_pts'][pt_value]=indices
        elif 'a' in str_var:
            defining_equations[int(str_var[1])]*=(pt_value)
            
    counter=0
    for i in range(0,5):
        while defining_equations[i].degree()<curve_deg:
            defining_equations[i]*=(t-fixed_vars['r_dict']['r'+str(counter)])
            counter+=1
    
    return defining_equations



#Improvements:  
"Perhaps use different description of ideal, rather than current one (one that gives more degenerate components that hopefully go away), maybe paired with facstd"
"Can alter slightly around minimal_primes computations.  Like in the loop, currently don't restrict the variables before finding minimal primes. So, could change this.  Also, could change exact computation of minimal primes (build it myself)"
"Also use different groebner basis algorithms if I've already computed one"
#parallelization

def main_curve(str1,base_fld=GF(101),div=False,acted_on_div=tuple((str(i) for i in range(7))),div_pairs=1,alt_conds=False,symmetry=True,Bound_Extra_Dim=0,Bound_Height=0,Bound_Degree_Field_Extension=12):
    global myRing
    global timedict
    #global new_nef_curves
    if div==1: #used to test classes we suspect are nef
        div_pairs=0 #This is done to ensure the appropriate expected dimension is calculated.
    startmain=time.time()
    if symmetry:  #Edit to actually incorporate Symmetry.  Also need to make sure action on divisor is same as action on curve.
        vect2,acted_on_curve=find_S7_rep(convert_to_vect(str1),'curve')
        #return vect2
    else:
        vect2=convert_to_vect(str1)
        acted_on_curve=tuple((str(i) for i in range(7)))
    print('acted on curve by',acted_on_curve)
    curve=convert_to_list(vect2)
    mon_conds,p5_conds=sep_curve(curve)
    roots=make_roots(vect2[0],mon_conds) #these are the variables for Exceptional Divs w/o 5
    p5_pts=make_p5_pts(p5_conds)
    acoeffs,free_acoeffs,base_fld=make_acoeffs(div,p5_conds[0],base_fld,acted_on_div,acted_on_curve)  #NEEEEEEDS EDITING TO INCORPORate what acutally happens with div
    #print curve
    
    if div:
        myRing=PolynomialRing(base_fld,list('t')+free_acoeffs+roots[::-1]+p5_pts)
    else:
        myRing=PolynomialRing(base_fld,list('t')+free_acoeffs+roots[::-1]+p5_pts[1:])
    faux_Fs,real_Fs=make_Fs(vect2[0],mon_conds,roots,acoeffs)
    ideal_gens=list()
    if alt_conds:
        alt_add_conds(ideal_gens,faux_Fs,acoeffs,p5_conds,div) #EDIT to actually write
    else:
        for i in range(0,5):
            for j in range(i+1,5):
                add_conds(ideal_gens,i,j,faux_Fs,acoeffs,p5_conds,div)  #EDIT TO INCORPORATE if div is TRUE, then also use p5_conds[0] first cond
                #instead, could just take remainder of Faux_F's I build by one single condition, and do for appropriate number of differences fi-fj (for each condition)
    #ima=ideal(ideal_gens)
    #ideal_gens=tuple(fix_auto_P1(ideal_gens,div,p5_pts,myRing.remove_var(myRing('t'))))
    #print ima.parent()
    #for elt in ima.gens():
    #    print elt, "is in ring", elt.parent(), '\n'
    print("main set up: up to this point, main took", time.time()-startmain, "seconds")
    print("number of p5_pts is",len(p5_pts)," and height of ideal they impose is ", sum((5-len(cond[0]))*cond[1] for cond in p5_conds), "maybe subtract",(5-len(p5_conds[0][0])),'if not using div')
    #Bound_Height=False
    if Bound_Height:
        if sum((5-len(cond[0]))*cond[1] for cond in p5_conds)>Bound_Height: #-(5-len(p5_conds[0][0]))>16:
            return False
    ideal_gens,fixed_vars,free_gens=fix_auto_P1(ideal_gens,div,p5_pts,myRing.remove_var(myRing('t')),base_fld)
    
    #Dimension of the subring that this ideal lives in is len(free_acoeffs)+len(roots)+len(p5_pts[1:])
    #The height of the ideal is (should be) (def bounded above by) 4*(#times hits p5) + 3*(#number times hits Li5) + 2*(#times hits Plane_ij5)
    #don't count the first p5 condition in calc of ht(ideal) above, because already accounted for with a's
    #Since we have only fixed 1 point on the curve, we can fix 2 more.  So either add these conds to the ideal, or use subs
    #Then, if we intersect the ideal+(set two vars to a constant) with (Dim(my_Ring)-ht(ideal)-2)) general hyperplanes... get 0-dimensional ideal
    #We should get an intersection point outside of the degenerate locus (ai=0, some marked pts = another marked point)
    
    
    #Start Random Stuff
    if div:
        j=len(free_gens)-sum(((5-len(cond[0]))*cond[1] for cond in p5_conds))+(div_pairs) #not +(div_pairs-1) because if fix extra point on div and curve, pairing decreases by 1.
    else:
        j=len(free_gens)-sum(((5-len(cond[0]))*cond[1] for cond in p5_conds))+(5-len(p5_conds[0][0]))+(div_pairs-1)
    #Bound_Extra_Dim=False
    if Bound_Extra_Dim:
        if j > Bound_Extra_Dim or j<0:
            return False
    
    done_random=False
    count=0
    
    #Bound_Degree=True
    while Bound_Degree_Field_Extension and not done_random and count<=4:
        while not done_random and count<=4: #count subject to change???
            done_random,data=random_process(ideal_gens,free_gens,j,base_fld,fixed_vars)
            if not done_random:
                print('random data failed to find nondegen points. Trying again')
                count+=1
        if count==5:
            print("total for this curve took ", time.time()-startmain, "seconds")
            print("Random process failed too many times. Did not test curve.")
            if div:
                return False#1
            else:
                return False#2
        #myLocRing,nondegen_pts,free_gens=*data
        myLocRing,nondegen_pts=data

        #Done Random, Now analyze points gotten.
        if done_random:
            chosen,min_deg=pick_lowDeg_nondegen_pt(nondegen_pts)
            if min_deg>Bound_Degree_Field_Extension:
                done_random=False
    
    while not done_random and count<=4: #count subject to change???
        done_random,data=random_process(ideal_gens,free_gens,j,base_fld,fixed_vars)
        if not done_random:
            print('random data failed to find nondegen points. Trying again')
            count+=1
    if count==5:
        print("total for this curve took ", time.time()-startmain, "seconds")
        print("Random process failed too many times. Did not test curve.")
        if div:
            return False#1
        else:
            return False#2
    #myLocRing,nondegen_pts,free_gens=*data
    myLocRing,nondegen_pts=data
    
    #Done Random, Now analyze points gotten.
    if done_random:
        chosen,min_deg=pick_lowDeg_nondegen_pt(nondegen_pts)
        final_pt=find_galois_representative(chosen,min_deg,myLocRing,base_fld.cardinality())
        my_PID=PolynomialRing(GF(base_fld.cardinality()**min_deg),'t')
        t=my_PID.gen()
        defining_equations=construct_curve_eqs(my_PID,t,fixed_vars,final_pt,vect2[0],acoeffs,div)  #EDIT FOR IF DIV IS TRUE
    
    print("main finished: up to this point, main took", time.time()-startmain, "seconds")
    print(defining_equations)
    print(fixed_vars['marked_pts'])
    
    for mrk_pt in fixed_vars['marked_pts']:
        print(tuple((polyy(mrk_pt) for polyy in defining_equations)))
    for polyy in defining_equations:
        print(polyy.factor())
    for j in range(2,5):
        print('changing p5 and ',j)
        aut_f=list()
        for i in range(0,5):
            if i != j:
                aut_f.append(defining_equations[j] - defining_equations[i])
            else:
                aut_f.append(defining_equations[j])
        for polyy in aut_f:
            print(polyy.factor())
    
    print("main took", time.time()-startmain, "seconds")
    
    #if not div:
    #    print(p5_pts[0], "unaccounted for in splitting type")
    
    return_lis,neg_curve,count=find_Normal_Bundle(my_PID, vect2[0], defining_equations, fixed_vars['marked_pts'],div,p5_conds[0][0]) #EDIT THIS TO INCORPORATE DIV!!!!!!
    
    #if not div:
    #    print(p5_pts[0], "unaccounted for in splitting type")
    
    
    print("total for this curve took ", time.time()-startmain, "seconds")
    
    #if not div:
    #    return [vect2[0],p5_conds[0][0],time.time()-startmain,return_lis]
    #else:
    #    return [vect2[0],'all conds accounted for',time.time()-startmain,return_lis]
    print("(Resolved) Normal Bundle:",return_lis)
    print('characteristic is', base_fld.characteristic())
    if count==0:
        print('curve is free/nef.  Has class: ', ' '.join((str(entry) for entry in vect2)))
        #new_nef_curves.add(' '.join((str(entry) for entry in vect2)))
        #print('new nef curves is', new_nef_curves)
    return neg_curve
    
#'''

def alt_add_conds(ideal_gens,faux_Fs,acoeffs,p5_conds,div):
    #adds constraints from fi-fj
    #make h, g, divide g by h, and let remainder = 0
    
    #TO CHANGE TO TAKING REMAINDER BY ONE THING AT A TIME, TRY THE FOLLOWING:
    #Still construct g in the same manner, but just iterate over p5 conditions, and select appropriate number of g to reduce
    #for instance, if its a plane, use only 2 g's, if its a line, use 3, f1-f2, f2-f3, f3-f4, but don't use the others
    #this could reduce the number of conditions we impose
    #the fact that use g, rather than fi-fj, actually doesn't matter.  It just lowers the degree of the generator, which is good
    #since use g, the difference will be dividing the remainder by z123-y123, for example.
    for i1,cond in enumerate(p5_conds):
        if i1==0 and not div:
            lower=1
        else:
            lower=0
        h1=myRing(1)
        indices='01234'
        for letter in cond[0][:-1]:
            indices=indices.replace(letter,'')
        for j in range(lower,cond[1]):
            h1*=(myRing('t')-myRing('z'+indices+'b'+str(j)))
        for i2 in range(len(indices)-1):
            i3=i2+1
            #""" #get rid of paragraph below if don't want this for alt conds--adds more polynomial conditions, possibly fewer degen components
            h=h1
            #could add more to h here--- like an inbetween idea, where h is built similar to before for fixed i and j
            '''h=h1
            enumerate over other conds just as did before, but skip the one indexed by i1.  really almost copy pasta from add_conds'''
            #"""
            for j1, cond2 in enumerate(p5_conds):
                if i1 != j1:
                    if str(i2) not in cond2[0]:
                        if str(i3) not in cond2[0]:
                            if j1==0 and not div:
                                lower1=1
                            else:
                                lower1=0
                            indices2='01234'
                            for letter in cond2[0][:-1]:
                                indices2=indices2.replace(letter,'')
                            for k in range(lower1,cond2[1]):
                                h*=(myRing('t')-myRing('z'+indices2+'b'+str(k)))
            #"""
            """
            h=h1 #another way to get rid of the differing idea for alt conds present in paragraph above"""
            
            #then construct g
            p1=faux_Fs[int(indices[i2])][:]
            p2=faux_Fs[int(indices[i3])][:]
            shared=list()
            for root in p1:
                if root in p2:
                    shared.append(root)
            for root in shared:
                p1.remove(root)
                p2.remove(root)
            g1=myRing(acoeffs[int(indices[i2])])
            g2=myRing(acoeffs[int(indices[i3])])
            for root in p1:
                g1*=(myRing('t')-root)
            for root in p2:
                g2*=(myRing('t')-root)
            g=g1-g2
            
            
            #then, reduce g by h
            polyn=g.reduce((h,))  #COULD THINK ABOUT DOING THIS FOR A SINGLE ROOT AT A TIME, SINCE LOCALIZE AWAY FROM BAD LOCUS
            #print polyn
            polyno=polyn.polynomial(myRing('t'))
    
            #finally:
            ideal_gens.extend(polyno.coefficients())


def construct_sub_mod(free_Mod,tgt_of_C,exceptional_div,pt_on_C):
    sub_mod_gens=list()
    #sub_mod_gens.append(tgt_of_C)
    for letter in exceptional_div:
        if letter != '5':
            sub_mod_gens.append(free_Mod.gen(int(letter)))
        else:
            #sub_mod_gens.append([1,1,1,1,1]) #may have to replace with my_PID(1),my_PID(1),... etc.
            sub_mod_gens.append(vector((1,1,1,1,1)))
    index=4
    checked_for_5=True #Don't set this to False.  Sometimes creates errors, and has next to no time-save.
    #perhaps change order in which use tgt of C and 5
    #checked_for_tgt_C=True #Only set if you don't want to include tgt directions, which should only be done for speed
    checked_for_tgt_C=True
    
    #while len(sub_mod_gens)<5: #reput this if include tangent beforehand
    while index>=0:
        if str(index) in exceptional_div:
            index-=1
        else:
            if tgt_of_C[index]!=0 and checked_for_tgt_C==False:
                checked_for_tgt_C=True
                index-=1
            else:
                if '5' in exceptional_div and checked_for_5==False:
                    checked_for_5=True
                    index-=1
                else:
                    sub_mod_gens.append(free_Mod.gen(index)*pt_on_C)
                    index-=1
    sub_mod_gens.append(tgt_of_C)
    #print index
    print(sub_mod_gens)
    return free_Mod.span(sub_mod_gens)
    #return free_Mod.submodule(sub_mod_gens)
        
    
def random_P1_auto(my_Ring,my_PID,defining_equations,marked_points,p5_pt):
    base_fld=my_PID.base_ring()
    new_pt=base_fld.random_element()
    while new_pt in marked_points.keys() or new_pt==base_fld(0):# or any((eqn(new_pt)==0 for eqn in defining_equations)):
        new_pt=base_fld.random_element()
    #want automorphism that interchanges s=0 and t-new_pt*s=0, while fixing .... what?  t=0? sure
    #s--->t/new_pt - s, t----> t,  gives scheme map v(s)--->v(t-new_pt*s) along with desired properties above.  Sends
    #v(t-alpha*s)------> v((s*new_pt-t)*alpha/new_pt + 1*t)=v(t+s*alpha/(1-alpha/new_pt))= v(t-s*(-alpha/(1-alpha/new_pt)))
    
    #So, set b=1/new_pt, and send      map:::::    (s---> b*t-s),   (t---->t),
    #giving v(t-a*s)----->v(t-(a/(a*b-1))*s)
    #thus, if precompose map of P1 into P4 with this map (yes, precompose because want to post compose the polynomial map), get desired map
    #So, need to change marked points to (a-----> a/(a*b-1)) and add point (p5_pt at t-s/b), and sub in for defining equations by the above map.
    #nooooo..... actually need preimage of v(t-a*s), which is v((1-a*b)*t + a*s) okay right its the same b/c map has order 2.
    
    
    #oooooorrrrr instead..... t-s------>t-s (so  s----> (a-1)*t+s), t-----> a*t (multiple of t) to send 1 to 1, 0 to 0, and new_pt to infinity
    #So for s---> t/new_pt -s, need -(a-1)=1/new_pt, i.e. a=1-1/new_pt
    #set b=1/new_pt, so   t----> (1-b)*t   and   s----> s-b*t
    #Then ring map is t - y*s ----> (1-b+y*b)*t-y*s === (b*(y-1)+1)*t - y*s ===== t-s*(y/(1-b+y*b))
    #So, if y== infinity, then its the appropriate point.
    #to figure out scheme map, set a=y/(1-b+y*b) and solve for y:  y=a*(1-b+y*b) implies y(1-a*b)=a*(1-b)  implies y = a*(1-b)/(1-a*b)
    #As a map of schemes,  v(t-a*s)-------> v(t-(a*(1-b)/(1-a*b))*s)  ==== v(t-(a*(b-1)/(a*b-1))*s) ===== v(t-(1-(a-1)/(a*b-1))*s)
    #Now, want to change v(t-y*s) into its preimage under the automorphism. So, phi^{-1}(v(t-y*s))=v(t-(y/(1-b+y*b))*s)
    
    #So, problem?  If y=-1/b + 1 = 1-new_pt, then  t-(1-new_pt)*s ----> (1-b)*t-(1-1/b)*(s-b*t)= (1-1/b)*s which is a problem
    #SO, actually, want inverse of that map, because it sends an unmarked point (new_pt) to infinity (s).
    #SO, inverse of the map is   t-a*s-------> t-(a*(1-b)/(1-a*b))*s, i.e. t----> t, and s---->b*t + (1-b)*s
    #[1-b  -b]
    #[0     1] has inverse 1/(1-b)[1  b][0  1-b] (so up to scalar I am right this time)
    #SOOOO actual map I want is t--->t, s-----> b*t + (1-b)*s, and t-a*s -------->(1-a*b)*t - a*(1-b)*s
    #I.e., in actual map, inverse image of t-a*s is t-(a*(1-b)/(1-a*b))*s (up to scalar)
    #So, if a is infinity, or just by looking at where s  is sent, see new point is t+((1-b)/b)*s = t-((b-1)/b)*s
    
    #So.... do I want (with b=1/new_pt):
    # phi(s)=(b*t-s) and phi(t)=t, and phi^{-1}(v(t-a*s))=v(t-(a/(a*b-1))*s) orrrrr...
    #phi(s)=(s-b*t) and phi(t)=((1-b)*t), and phi^{-1}(v(t-a*s))=v(t-(a/(a*b-b+1))*s)  #####CHOOSE THIS ONE  #NEVERMIND WRong mAP
    
    #Right map:
    #phi(s)=(b*t-(b-1)*s) and phi(t)=(t), and phi^{-1}(v(t-a*s))=v(t-(a*(1-b)/(1-a*b))*s)
    #So, new marked point to add is (b-1)/b=1-new_pt, and we see that t-(1/b)*s ----> s*(b-1)/b
    b=1/new_pt  #base_fld(1)/new_pt
    new_marked_pts=dict({(1-new_pt):p5_pt})
    for key,value in marked_points.items():
        new_key=key*(1-b)/(1-key*b)
        new_marked_pts[new_key]=value #or use .update()
    
    #Then, handle defining equations:
    new_defining_equations=list()
    t=my_Ring('t')
    s=my_Ring('s')
    for eqn in defining_equations:
        polyn=eqn.homogenize('s').subs({s:(b*t-(b-1)*s)}).specialization({s:1})
        new_defining_equations.append(polyn)
    
    #This should be it!!!
    return new_marked_pts,new_defining_equations
        
        
        
def check_strict_transform(marked_points,defining_equations,degree):
    #check that the gcd of various pairs, etc of defining equations are of the correct degree.  Also, check that no 3 def equations have the same leading coefficient
    #maybe also use degree, to ensure s is not a point.
    #need to check this for changing 5 with 2,3,4.  Not for others, but might as well check regular, no change too.
    
    #check that degree of defining eqs is right, and the thing about leading coeff here.
    leading_coeffs=dict()
    count=0
    for polyn in defining_equations:
        if polyn.degree() > degree:
            print("Error: Curve not of expected degree! Too high!")
            return False
        elif polyn.degree()<degree:
            count+=1
        else:
            leading_coeffs[polyn.lc()]=leading_coeffs.get(polyn.lc(),0)+1
    if count>=2:
        print('Error: s hits plane')
        return False
    for value in leading_coeffs.values():
        if value > 2:
            print('Error: too many leading coeffs the same')
            return False
    
    def expected_degree(sublis_pt,switched):
        expected_deg=0
        for value in marked_points.values():
            if not any((str(elt) in value for elt in sublis_pt)):
                if str(switched) not in value:
                    expected_deg+=1
        return expected_deg
    
    def check_gcd(lis_pt,aut_f,switched):
        for i1 in range(0,5):
            g1=aut_f[i1]
            sublis1=(lis_pt[i1],)
            for i2 in range(i1+1,5):
                g2=g1.gcd(aut_f[i2])
                sublis2=sublis1+(lis_pt[i2],)
                if g2.degree() != expected_degree(sublis2,switched):
                    print('correct mult false from',sublis2,g2)
                    print(g2.degree(),expected_degree(sublis2,switched))
                    return False
                for i3 in range(i2+1,5):
                    g3=g2.gcd(aut_f[i3])
                    sublis3=sublis2+(lis_pt[i3],)
                    if g3.degree() != expected_degree(sublis3,switched):
                        print('correct mult false from',sublis3,g3)
                        print(g3.degree(),expected_degree(sublis3,switched))
                        return False
                    for i4 in range(i3+1,5):
                        g4=g3.gcd(aut_f[i4])
                        sublis4=sublis3+(lis_pt[i4],)
                        if g4.degree() != expected_degree(sublis4,switched):
                            print('correct mult false from',sublis4,g4)
                            print(g4.degree(),expected_degree(sublis4,switched))
                            return False
                        for i5 in range(i4+1,5):
                            g5=g4.gcd(aut_f[i5])
                            sublis5=sublis4+(lis_pt[i5],)
                            if g5.degree() != expected_degree(sublis5,switched):
                                print('correct mult false from',sublis5,g5)
                                print(g5.degree(),expected_degree(sublis5,switched))
                                return False
        return True
    
    correct_mult=True
    for j in range(2,5):
        aut_f=list()
        for i in range(0,5):
            if i != j:
                aut_f.append(defining_equations[j] - defining_equations[i])
            else:
                aut_f.append(defining_equations[j])
        lis_pt=list(range(0,5))
        lis_pt[j]=5
        if correct_mult:
            correct_mult=check_gcd(lis_pt,aut_f,j)
    if correct_mult:
        correct_mult=check_gcd(list(range(0,5)),defining_equations,5)
    #if it makes it to this point, then the strict transform of the curve is the right class!
    return correct_mult
    
    

def find_Normal_Bundle(my_PID, degree, defining_equations, marked_points,div,p5_pt,check_mult=True):
    time_construct=0
    time_simplify=0
    time_intersect=0
    time_groebner=0
    
    my_Ring=my_PID.extend_variables('s')
    #'''
    if not div:
        marked_points,defining_equations=random_P1_auto(my_Ring,my_PID,defining_equations,marked_points,p5_pt)
    #'''
    if check_mult:
        correct_mult=check_strict_transform(marked_points,defining_equations,degree)
        print(correct_mult,"is correct mult")
        
        for polyy in defining_equations:
            print(polyy.factor())
        for j in range(2,5):
            print('changing p5 and ',j)
            aut_f=list()
            for i in range(0,5):
                if i != j:
                    aut_f.append(defining_equations[j] - defining_equations[i])
                else:
                    aut_f.append(defining_equations[j])
            for polyy in aut_f:
                print(polyy.factor())
        
        if correct_mult==False:
            return [],correct_mult,2 #added "count=2" to make compatible
    
    
    #input is a polyring my_PID, the degree of the curve, the defining equations of the curve as elements in my_PID, and a dictionary of {"ijk":elt_in_base_field, "ij":....} of marked points.
    #make sure that $s=0$ is not one of the fixed points.
    #This algorithm replaces the normal bundle of the curve with the middle term in the Euler Sequence, then finds the splitting type of the sub-bundle whose quotient is the normal bundle of the blow up
    #To do this, we define a free module of rank 5 over k[t], where k is the base field.  Then, for each marked point, we
    #construct the sub-bundle of this free module that is twisted down by the marked points in directions complimentary to that of the tgt space of the curve and linear subspace.
    #then, we intersect all such submodules, and attain the appropriate bundle.
    t=my_PID.gen()
    #free_Mod=FreeModule(my_PID,5)
    free_Mod=my_PID**5
    #B=free_Mod.basis()
    #t_deriv_Fs=PolynomialSequence((polyn.derivative(t) for polyn in defining_equations),my_PID)
    t_deriv_Fs=tuple((polyn.derivative(t) for polyn in defining_equations))
    
    normal_Bundle=free_Mod
    #try diff method
    
    list_of_submods=list()
    #end try diff method 
    
    #for key,value in marked_points.items(): #changed what I wanted key and value to be
    for value,key in marked_points.items(): #changed what I wanted key and value to be
        #tgt_of_C=vector(t_deriv_Fs.subs(t=value))
        tgt_of_C=vector((polyn(value) for polyn in t_deriv_Fs))
        start1=time.time()
        new_sub_mod=construct_sub_mod(free_Mod,tgt_of_C,key,t-value)
        time_construct+=time.time()-start1
        if new_sub_mod.rank() != 5:
            print("Error, did not get a rank 5 sub bundle!!! Tgt Vector of C was linearly dependent with other choices.")
            print(tgt_of_C)
            print(key,value)
            print(new_sub_mod)
            print(new_sub_mod.gens())
            t_mult_derivs_Fs=t_deriv_Fs
            counter=2
            while new_sub_mod.rank() !=5 and t_mult_derivs_Fs != tuple((0,0,0,0,0)):
                t_mult_derivs_Fs=tuple((polyn.derivative(t) for polyn in t_mult_derivs_Fs))
                tgt_of_C=vector((polyn(value) for polyn in t_mult_derivs_Fs))
                start1=time.time()
                new_sub_mod=construct_sub_mod(free_Mod,tgt_of_C,key,(t-value)**counter)
                time_construct+=time.time()-start1
                print('curve is tangent to boundary to ', counter, ' order, and normal bundle  at point is ',new_sub_mod)
                print(tgt_of_C)
                counter+=1
        if new_sub_mod.rank() != 5:
            print("Error: rank new_sub_mod still not 5.  Discarding this marked point.")
        else :
            list_of_submods.append(Sequence(vector(my_Ring, elt.list()) for elt in new_sub_mod.gens()))
        start1=time.time()
        "stand_in=normal_Bundle.intersection(new_sub_mod)"
        time_intersect+=time.time()-start1
        #print stand_in.gens()
        #print normal_Bundle.gens()
        start1=time.time()
        "normal_Bundle=simplify_gens(free_Mod,stand_in)"
        time_simplify+=time.time()-start1
        #list_of_submods.append(new_sub_mod)
        #list_of_submods.append(Sequence(vector(my_Ring, elt.list()) for elt in new_sub_mod.gens()))
        #normal_Bundle=free_Mod.submodule(normal_Bundle.gens())
        #print normal_Bundle.gens(), "\n\n\n\n\n\n"
    '''
    #Add cond about divisor being false:
    if not div:
        #s_deriv_Fs=tuple((polyn.homogenize('s').subs({t:1}).derivative(my_Ring('s')) for polyn in defining_equations))
        #s_deriv_Fs=tuple((polyn.derivative(my_Ring('s')) for polyn in ))
        tgt_of_C=tuple((polyn.homogenize('s').derivative(my_Ring('s')).specialization({t:1})(0) for polyn in defining_equations))
        new_sub_mod=construct_sub_mod(FreeModule(my_Ring.remove_var(t),5),tgt_of_C,p5_pt,my_Ring('s').specialization({t:1}))
        if new_sub_mod.rank() != 5:
            print("Error, did not get a rank 5 sub bundle!!! Tgt Vector of C was linearly dependent with other choices.")
            print(tgt_of_C)
            print(key,value)
            print(new_sub_mod)
            print(new_sub_mod.gens())
        else :
            list_of_submods.append(Sequence(vector(my_Ring, elt.list()) for elt in new_sub_mod.gens()))
    #'''
    #print normal_Bundle.gens() #Can instead find the degree of these gens later, for more advanced program.
    #for elt in normal_Bundle.gens():
    #    print elt
    #    print module_elem(free_Mod,[elt.get(i1) for i1 in range(0,5)])
    #my_Ring=my_PID.extend_variables('s') #it is necessary to change the basering of the module, because singular won't handle conversion from k[t]
    start1=time.time()
    #module2=intersect1(*list_of_submods)
    module1=intersect1(*list_of_submods)
    print("Singular intersection took", time.time()-start1, "seconds.  Below is the result:")
    #print module2
    #module1=Sequence((module_elem(free_Mod,[elt.get(i1) for i1 in range(0,5)]) for elt in normal_Bundle.gens()))
    #module1=Sequence(elt.change_ring(my_Ring) for elt in normal_Bundle.gens())
    "module1=Sequence(vector(my_Ring, elt.list()) for elt in normal_Bundle.gens())"
    #print module1
    print("\n\n\n\n")
    #for elt in module1:
    #    print elt
    #    print elt.parent() #if previously interupted kernel, and try to use groebner1, then base_ring will not be defined. Just run it again
    #print groebner1(module1)
    start1=time.time()
    grob=groebner1(module1)
    time_groebner+=time.time()-start1
    print("Singular intersection returns groebner basis is ", grob==module1)
    
    '''
    #Add cond about divisor being false:
    if not div:
        #s_deriv_Fs=tuple((polyn.homogenize('s').subs({t:1}).derivative(my_Ring('s')) for polyn in defining_equations))
        #s_deriv_Fs=tuple((polyn.derivative(my_Ring('s')) for polyn in ))
        tgt_of_C=tuple((polyn.homogenize('s').derivative(my_Ring('s')).specialization({t:1})(0) for polyn in defining_equations))
        new_sub_mod=construct_sub_mod(FreeModule(my_Ring.remove_var(t),5),tgt_of_C,p5_pt,my_Ring('s').specialization({t:1}))
        if new_sub_mod.rank() != 5:
            print("Error, did not get a rank 5 sub bundle!!! Tgt Vector of C was linearly dependent with other choices.")
            print(tgt_of_C)
            print(key,value)
            print(new_sub_mod)
            print(new_sub_mod.gens())
        grob2=groebner1(Sequence(vector(my_Ring, elt.list()) for elt in new_sub_mod.gens()))
        module1=intersect1(module_homog(my_Ring,grob,my_Ring('s')),module_homog(my_Ring,grob2,t))
        grob=groebner1(module1)
    #'''  
    for elt in grob:
        print(elt)
    return_lis=list()
    for elt in grob:
        max_deg=0
        basis_vec=0
        for i1, coordi in enumerate(elt.list()):
            if coordi.degree() >= max_deg:
                max_deg=coordi.degree()
                basis_vec=i1
        print(max_deg, "at coordinate vector", basis_vec)
        #return_lis.append(str(max_deg)+"at coordinate vect"+str(basis_vec))
        return_lis.append(tuple((degree-max_deg,'basis vect='+str(basis_vec))))
    
    #now check if it is a negative curve:
    count=0
    neg_curve=True
    if len(return_lis)!=5:
        print("Error: too many/few generators for (resolved) normal bundle given by groebner basis.")
        neg_curve=False
    set_basis=set()
    for elt in return_lis:
        if elt[0]<0:
            count+=1
        set_basis.add(elt[1])
    if len(set_basis)!=5:
        print("Error: rank of (resolved) normal bundle is not 5.")
        neg_curve=False
    if count==0:
        print("Error: the (resolved) normal bundle has all nonnegative factors in splitting type.  Not neg curve")
        neg_curve=False
    elif count>1:
        print("Unexpected (not really Error): the (resolved) normal bundle has more than 1 (exactly", count, ") negative factors.  Not negative curve")
        neg_curve=False
    if neg_curve:
        print("Found Negative Curve!")
    
    
    print("time spent constructing submods was", time_construct)
    print("time spent simplifying gens was", time_simplify)
    print("time spent intersecting bundles was ", time_intersect)
    print("time spent computing groebner basis ", time_groebner)
    print("\n\n\n\n\n")
    return return_lis,neg_curve,count




#END SECTION FOR CURVES::::::::::::::::::::::::::::::::::::::::::::::::::::

#BEGIN SECTION FOR PROCESSING DIV & CURVE TOGETHER
def eval_mult(polyn,non_gens):
    #evaulate the muultiplicity of a polynomial on a monomial ideal.  
    #non_gens is the list of generators that are notin the monomial ideal.
    poly_mult=polyn.degree()
    subtrac=0
    for elt in polyn.exponents(): #in polyn.exponents(as_ETuples=False)
        if sum(elt[i] for i in non_gens)>subtrac:
            subtrac=sum(elt[i] for i in non_gens)
    poly_mult-=subtrac
    return -poly_mult

def poly_To_Vect(polyn):
    vect1=list()
    vect1.append(polyn.degree())
    x0,x1,x2,x3,x4=polyn.parent().gens()
    polyn4=polyn.subs({x0:x4-x0,x1:x4-x1,x2:x4-x2,x3:x4-x3})
    polyn3=polyn.subs({x0:x3-x0,x1:x3-x1,x2:x3-x2,x4:x3-x4})
    polyn2=polyn.subs({x0:x2-x0,x1:x2-x1,x3:x2-x3,x4:x2-x4})
    for i in range(0,5):
        vect1.append(eval_mult(polyn,(i,)))
    vect1.append(eval_mult(polyn4,(4,)))
    for i in range(0,6):
        for j in range(i+1,6):
            if j!=5:
                vect1.append(eval_mult(polyn,tuple((i,j))))
            else:
                if i!=4:
                    vect1.append(eval_mult(polyn4,tuple((i,4))))
                else:
                    vect1.append(eval_mult(polyn3,tuple((3,4))))
    for i in range(0,6):
        for j in range(i+1,6):
            for k in range(j+1,6):
                if k!=5:
                    vect1.append(eval_mult(polyn,tuple((i,j,k))))
                else:
                    if j!=4:
                        vect1.append(eval_mult(polyn4,tuple((i,j,4))))
                    else:
                        if i!=3:
                            vect1.append(eval_mult(polyn3,tuple((i,3,4))))
                        else:
                            vect1.append(eval_mult(polyn2,tuple((2,3,4))))
    return vect1


#have convert_to_dict(takes vector)
#convert_to_str(takes frozenset,obj)
#convert_to_frz(takes vector,obj)

def S7_acts_on_vect_div(vect1,perm1):
    #acts by perm1.
    div=dict(convert_to_frz(vect1,'div'))
    #this would be if acting by inverse of perm1
    for i1,elt in enumerate(perm1):
        if elt=='6':
            change6=str(i1)
    perm=dict()
    for i in range(6):
        perm[str(i)]=perm1[i]
    
    #instead act by perm1:
    #perm=dict()
    #change6=perm1[6]
    #for i in range(6):
    #    perm[perm1[i]]=str(i)
    
    if change6!='6':
        perm[change6]=perm1[6]
    
    
    div3=[]
    for coord in div.items():
        if coord[0] != 'd':
            sentTo=[]
            for letter in coord[0]:
                sentTo.append(perm[letter])
            sentTo.sort()
            permuted=''.join(sentTo)
            div3.append(tuple((coord[0],div[permuted])))
        else:
            div3.append(coord)
    div=dict(div3)
            
    if change6 != '6':
        div3=[]
        for coord in div.items():
            if change6 in coord[0]:
                div3.append(coord)
            elif coord[0]=='d':
                indices='012345'.replace(change6,'')
                div3.append(tuple(('d',4*div['d']-sum(div[letter] for letter in indices))))
            else:
                indices='012345'.replace(change6,'')
                for letter in coord[0]:
                    indices=indices.replace(letter,'')
                if len(coord[0])==1:
                    div3.append(tuple((coord[0],(len(indices)-1)*div['d']-sum(div[letter] for letter in indices))))
                else:
                    div3.append(tuple((coord[0],(len(indices)-1)*div['d']+div[indices]-sum(div[letter] for letter in indices))))
        #div=dict(div3)
    
    #now, update acted_by
    new_div=convert_to_str(frozenset(div3),'div')
    #print(new_div)
    return convert_to_vect(new_div)

def process_div_list(list_poly,acted_on_div):
    return_lis=list()
    for elt in list_poly[0]:
        return_lis.append(tuple((elt,S7_acts_on_vect_div(poly_To_Vect(elt),acted_on_div))))
    return return_lis


def process_div_curve(str_div='',str_curve='',expect_nef=False):
    if str_div:
        dimensi,list_poly,acted_on_div1=main_div(str_div,1,base_fld=QQ,symmetry=True)
        if dimensi==0:
            print('Div not effective')
            return False
        div_candids=process_div_list(list_poly,acted_on_div1)
        if not str_curve:
            print('divisor breaks into components with classes:')
            for div_poly,div_vect in div_candids:
                print(' '.join((str(entry) for entry in div_vect)))
        else:
            line=str_curve
            count=0
            min_pair=0
            min_poly=False
            div_vec=("No Div--Error",)
            curve_vect=convert_to_vect(line)
            for div_poly,div_vect in div_candids:
                temp_sum=sum(div_vect[i]*curve_vect[i] for i in range(len(curve_vect)))
                if temp_sum<0:
                    count+=1
                if temp_sum<min_pair:
                    min_pair=temp_sum
                    min_poly=div_poly
                    div_vec=div_vect
                if count==0:
                    print("ERROR!  CURVE DID NOT PAIR NEGATIVELY WITH ANY DIVISOR CANDIDATE")
                    print('curve: \n',curve_vect)
                    print('div: \n',div_candids)
                    print('acted_on_div: ',acted_on_div1)
                    print('orig_div: \n',convert_to_vect(str_input))
                elif count>1:
                    print("CURVE PAIRED NEGATIVELY WITH TWO OR MORE DIV CANDIDATES--SKIPPING")
                elif count==1:
                    result_test=main_curve(line,base_fld=GF(101),div=min_poly,acted_on_div=acted_on_div1,div_pairs=-min_pair,symmetry=True,alt_conds=False)
                    if result_test==False:
                        result_test=main_curve(line,base_fld=GF(101),div_pairs=-min_pair)  
                    if result_test==True:
                        str_div=' '.join((str(entry) for entry in div_vec))
                        print('The following is an extreme divisor, negative curve pair: \n     Extreme Divisor: ', str_div, '\n      Negative Curve: ', line)
    elif str_curve:
        line=str_curve
        if expect_nef:
            result_test=main_curve(line,div=1,div_pairs=0)
        else:
            result_test=main_curve(line)
        if result_test:
            print('Possible Negative curve: ', str_curve)
        else:
            print('Did not find possible negative curve.')

#EXAMPLES
#candids={'5 0 0 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 2 1 0 2 0 2 2 0 0 2 0 1 0 3 2 0 0 1 0 0 0':'17 -10 -12 -10 -11 -11 -8 -5 -8 -4 -6 -5 -5 -8 -6 -3 -5 -5 -5 -5 -2 -6 -4 -1 -5 0 -4 -5 -3 -1 -2 -1 -2 -1 -3 -5 -2 -1 -4 0 0 0','7 0 0 0 0 0 0 1 0 1 1 2 0 0 2 0 2 1 2 2 0 0 2 0 0 0 0 0 0 0 0 1 0 0 0 0 3 0 0 0 0 0':'14 -7 -8 -8 -9 -8 -7 -5 -2 -6 -3 -5 -2 -3 -6 -5 -8 -6 -6 -7 -3 -2 -2 0 -1 -3 -1 0 0 -1 0 -2 -2 0 0 -1 -3 0 -5 -2 0 0'}
#candids={'5 0 0 0 0 0 0 1 1 0 0 0 1 0 0 0 0 0 0 0 0 0 0 2 0 0 0 2 0 0 2 2 0 0 2 2 0 2 2 2 0 1':'9 -5 -5 -5 -5 -5 -5 -3 -3 -3 -3 -3 -3 -3 -3 -3 -3 -3 -3 -3 -3 -3 -1 -2 -1 -1 -1 -2 -1 -1 -2 -2 -1 -1 -2 -2 -1 -2 -2 -2 -1 -1'}
div_curve_dict={'6 -4 -4 -4 -3 -3 -2 -3 -4 -1 -3 -1 -3 -2 -2 -2 -3 -1 -1 -2 -1 -1 -2 0 -1 0 -1 -1 -1 0 0 0 -1 0 0 -2 0 0 0 0 0 0':'5 0 0 0 0 0 0 1 1 0 2 0 1 0 0 1 2 0 0 0 1 1 0 0 0 0 0 0 1 0 0 0 0 0 0 2 0 0 0 0 0 0',
 '5 -4 -3 -2 -3 -3 -2 -3 -1 -2 -3 -1 -1 -2 -1 -2 -2 -1 -1 -1 -1 -1 0 -2 -1 -1 -1 0 -1 -1 0 0 0 -1 0 0 0 0 -1 0 0 0':'5 0 0 0 0 0 0 1 0 0 2 0 0 0 0 1 2 0 0 0 1 1 0 2 0 0 0 0 2 0 0 0 0 2 1 0 0 0 1 0 0 0',
 '4 -3 -2 -2 -2 -2 -2 -1 -1 -1 -2 -2 0 -2 -1 -2 -2 -1 -2 -1 0 0 0 -1 0 -1 -1 0 -1 0 0 0 0 0 0 -1 0 0 -1 0 0 0':'5 0 0 0 0 0 0 0 0 0 2 1 0 0 0 2 1 0 2 0 0 0 0 2 0 0 0 0 0 0 0 0 0 1 0 1 0 0 2 0 0 0',
 '9 -5 -5 -6 -5 -5 -4 -3 -4 -2 -2 -4 -4 -4 -1 -2 -2 -5 -3 -3 -2 -1 -3 0 0 -1 0 -1 -1 -2 -1 -1 -1 -1 -1 0 0 -1 -1 -2 0 0':'5 0 0 0 0 0 0 0 1 0 0 1 0 2 0 1 0 2 0 1 0 0 2 0 0 0 0 0 0 1 1 1 0 0 0 0 0 1 0 2 0 0',
 '6 -4 -3 -3 -3 -3 -3 -1 -1 -1 -3 -3 0 -3 -2 -3 -3 -2 -3 -2 0 0 0 -1 0 -1 -1 0 -1 0 0 0 0 0 0 -1 0 0 -1 0 0 0':'8 2 0 0 0 0 0 0 0 0 1 2 0 2 1 2 2 1 2 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1',
 '14 -7 -8 -8 -9 -8 -7 -5 -2 -6 -3 -5 -2 -3 -6 -5 -8 -6 -6 -7 -3 -2 -2 0 -1 -3 -1 0 0 -1 0 -2 -2 0 0 -1 -3 0 -5 -2 0 0':'7 0 0 0 0 0 0 1 0 1 1 2 0 0 2 0 2 1 2 2 0 0 2 0 0 0 0 0 0 0 0 1 0 0 0 0 3 0 0 0 0 0',
 '6 -3 -3 -4 -4 -4 -3 -2 -2 -1 -2 -2 -2 -2 -1 -2 -2 -2 -2 -3 -1 -1 -1 -1 -1 -1 0 -2 0 0 -1 -1 -2 0 0 0 -1 -1 -2 0 0 0':'5 0 0 1 0 0 0 0 0 0 0 1 0 0 0 1 0 0 1 2 0 0 1 1 1 0 0 2 0 0 2 0 2 0 0 0 0 2 0 0 0 0',
 '6 -4 -4 -3 -4 -3 -3 -3 -2 -2 -2 -3 -2 -3 -1 -2 -1 -2 -1 -2 -1 -1 -2 -1 -1 -1 0 0 0 -2 -1 -1 -1 0 -1 0 0 -1 0 -1 0 0':'5 0 0 0 1 0 0 0 0 0 0 2 0 1 0 1 0 2 0 0 0 0 2 0 1 0 0 0 0 2 0 0 1 0 0 0 0 1 0 1 1 0', 
 '6 -3 -4 -3 -4 -3 -3 -3 -2 -2 -2 -3 -2 -3 -1 -2 -1 -2 -1 -2 -1 -1 -2 -1 -1 -1 0 0 0 -2 -1 -1 -1 0 -1 0 0 -1 0 -1 0 0':'5 0 0 0 0 0 0 0 1 0 0 2 0 2 0 0 0 2 0 0 0 0 1 0 1 0 0 0 0 2 1 0 1 0 1 0 0 2 0 1 0 0',
 '8 -4 -5 -5 -5 -5 -4 -3 -3 -3 -1 -2 -2 -2 -3 -3 -3 -2 -3 -4 -1 -1 -2 -2 -1 -1 -3 0 -1 0 -1 -1 0 -2 0 -1 -1 -1 -2 0 0 0':'5 0 0 0 0 0 0 0 0 0 0 1 0 0 1 1 0 0 2 2 0 0 1 2 0 0 2 0 0 0 0 2 0 1 0 0 1 0 1 0 0 0'}

neg_curves={'4 0 0 0 0 0 0 0 0 0 0 0 0 1 2 0 0 0 1 0 1 0 0 0 0 2 1 2 1 1 0 0 1 0 0 0 0 0 0 0 0 0', '4 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 1 0 0 1 1 0 1 2 0 2 0 1 0 0 1 0 1 1 0 1 0 1 0 0 0', '5 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0 1 0 2 1 0 3 0 2 0 1 0 2 0 0 0 2 0 1 0 2 0 0 0', '5 0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 1 1 0 1 0 2 0 1 2 1 0 1 0 0 2 0 1 0 2 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 2 0 0 0 0 0 0 1 0 0 0 1 0 0 1 0 0 0 0 2 2 0 0 2 1 1 0 2 2 1 0 1 0 0 0', '5 0 0 0 0 1 0 0 0 0 0 0 0 0 0 1 0 2 1 0 1 0 1 2 0 1 2 0 1 0 0 0 0 0 0 2 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 1 0 0 0 0 2 2 0 0 0 1 0 1 0 0 0 0 2 1 2 1 1 0 0 1 0 0 0 0 0 0 0 0 0', '4 0 0 0 0 0 0 2 0 0 0 0 0 0 0 0 0 0 1 0 1 1 0 0 0 1 0 1 0 2 0 0 2 1 0 0 0 0 1 0 0 0', '5 0 0 0 0 0 0 2 0 0 0 0 0 1 0 0 2 0 1 0 0 2 0 0 0 1 0 2 0 1 1 0 0 1 1 1 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 2 0 0 0 1 2 1 1 1 1 0 2 0 0 1 0 0 1 2 2 0 0 0 0 0 0', '5 0 0 0 0 0 0 1 0 0 1 0 1 1 0 0 1 0 0 0 0 2 0 0 0 1 1 2 0 0 2 0 0 0 2 2 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 2 0 0 0 0 0 2 0 0 1 0 0 2 1 0 1 0 1 0 0 1 2 0 0 2 0 1 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 2 0 0 0 2 0 0 0 0 2 0 0 0 0 1 0 0 0 0 0 2 0 1 1 0 0 1 1 2 0 0 0 0 0 0', '3 0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0 1 0 1 0 0 1 1 0 1 0 0 1 0 1 0 1 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 2 0 2 0 0 2 0 0 0 1 1 0 0 1 0 0 1 0 2 0 0 0 0 2 0 0 0 0 0 0 0 0 0', '3 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 1 1 0 0 1 0 0 0 1 1 0 0 1 1 0 0 1 0 0 0 0 0 0 0 0 0', '4 0 0 1 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 1 0 1 0 2 0 1 0 2 1 0 2 0 1 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 0 0 2 1 2 0 0 0 2 0 0 0 1 0 0 2 0 2 0 0 1 1 0 0 0 1 0 0 0 0 0 0 0', '3 0 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 1 0 1 1 0 0 1 0 1 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0', '4 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 2 1 0 0 1 1 0 1 1 1 0 0 2 0 0 1 0 0 1 0 0 0', '5 0 0 0 0 0 0 2 0 0 0 0 0 0 0 0 1 0 0 2 0 2 0 1 0 0 1 1 2 0 1 0 0 2 1 0 1 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 2 0 0 1 0 2 0 0 0 1 0 1 1 0 0 0 2 0 2 1 1 0 0 2 0 0 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 2 0 0 0 0 0 0 0 0 0 1 0 0 1 2 0 0 0 1 1 2 0 1 1 0 2 0 2 2 0 0 0 0 0 0', '3 0 0 0 0 0 0 0 0 0 1 0 0 0 1 0 0 0 1 1 1 0 1 0 0 1 1 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 0 1 0 0 2 0 0 0 0 2 2 1 0 1 0 0 2 0 2 0 0 0 0 0 1 0 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 2 0 0 0 0 1 0 0 1 2 0 0 0 0 1 0 0 0 0 0 2 0 1 2 1 0 0 1 2 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 0 2 0 0 0 2 0 0 0 1 1 0 0 1 0 0 1 2 0 0 0 2 0 2 0 2 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 2 0 0 0 1 2 0 1 1 1 1 2 0 0 1 0 0 1 2 2 0 0 0 0 0 0', '5 0 0 0 1 0 0 2 0 0 0 0 0 0 0 0 1 0 1 0 0 2 0 0 0 1 1 2 0 0 1 0 0 1 1 2 0 0 0 0 0 0', '4 0 0 0 0 0 0 1 0 0 0 0 0 0 1 0 2 0 1 0 0 1 0 1 0 1 0 2 0 0 1 0 0 0 1 1 0 0 0 0 0 0', '4 0 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 1 0 1 2 0 0 0 1 0 1 1 1 1 2 0 1 0 2 0 0 0', '5 0 0 0 0 0 0 0 0 0 1 0 0 2 0 0 0 0 2 0 1 0 1 0 0 2 2 0 0 2 0 0 0 3 0 0 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 2 1 0 2 0 2 2 0 0 2 0 1 0 3 2 0 0 1 0 0 0'}

nef_curves={'3 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0 1 0 1 0 0 1 1 1 1 0 0 1 0 0 0 1 0 0 0 0 0 0 0', '2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 1 0 1 0 0 1 0 1 1 0 1 0 1 0 0 0', '4 0 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 2 0 0 0 1 0 1 2 1 1 2 0 1 0 2 0 0 0', '4 0 0 0 0 0 0 0 0 1 0 0 0 0 1 0 0 0 1 1 1 1 0 1 0 1 0 2 0 0 0 0 2 0 0 0 0 0 0 0 0 0', '4 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 1 0 2 1 0 0 2 0 0 1 0 0 1 1 1 0 0 0 0 0 0', '3 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 2 0 0 2 1 1 0 2 2 0 0 0 0 0 0', '4 0 0 0 0 0 0 0 0 1 0 0 0 0 1 0 1 0 0 0 1 0 1 0 2 1 0 0 0 0 1 0 0 0 2 0 0 0 2 0 0 0', '4 0 0 0 0 0 0 0 1 0 0 0 0 1 1 0 0 1 0 0 0 0 0 0 1 0 2 0 0 0 1 2 0 0 2 1 1 0 0 0 0 0', '4 0 0 0 0 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 1 0 1 0 0 1 2 1 0 1 1 1 1 0 2 1 0 0 0 0 0 0', '4 0 0 0 0 0 1 0 0 1 0 0 1 0 0 0 0 0 0 0 0 1 0 1 0 0 1 2 0 0 1 0 0 0 1 2 0 0 0 0 0 0', '3 0 0 0 0 0 0 0 1 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 1 0 1 0 0 0 1 1 1 0 2 0 0 0 0 0 0 0', '3 0 0 0 0 0 1 0 0 0 1 0 1 0 0 0 0 0 0 1 0 0 0 1 0 1 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0 0', '4 0 0 0 0 0 0 1 0 0 0 1 0 0 0 0 0 0 0 0 0 1 0 0 0 1 2 2 0 0 1 0 1 0 1 3 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 1 0 2 0 0 0 0 0 0 0 0 0 0 2 0 2 0 1 0 0 0 0 1 0 2 0 3 1 0 0 2 0 0 0', '5 0 0 0 0 0 1 0 0 0 1 0 0 1 0 0 0 0 0 0 0 0 1 0 0 0 2 2 0 0 2 1 0 1 3 3 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 0 0 0 1 2 1 0 0 0 0 0 0 1 0 0 0 0 2 3 0 0 3 1 0 0 2 1 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 0 1 1 2 0 0 0 0 0 0 0 0 1 0 0 1 0 3 1 0 0 1 1 0 0 2 3 1 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2 0 0 0 0 2 2 0 1 0 1 1 0 1 2 0 0 0 3 3 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 2 0 1 1 3 0 0 0 3 0 0 1 1 0 0 3 0 1 0 0 0 0 0', '5 0 0 0 0 0 0 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3 0 0 3 1 2 0 3 3 0 0 0 0 0 0', '5 0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0 0 1 0 1 0 0 1 0 1 1 3 0 0 2 0 0 0 2 3 0 0 0 0 0 0', '5 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 0 1 0 0 1 3 0 0 1 1 0 2 3 2 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 1 0 2 0 0 0 1 0 0 0 0 0 0 1 0 2 0 1 0 0 0 0 2 0 2 0 3 0 0 0 2 0 0 0', '5 0 0 0 0 0 0 0 2 1 0 0 0 0 0 1 0 0 0 0 0 0 0 0 2 0 0 1 0 0 2 2 2 0 2 2 0 0 1 0 0 0', '5 0 0 0 0 0 0 1 0 0 1 1 0 0 0 0 0 1 0 0 0 1 0 0 1 0 2 1 0 0 2 0 2 0 3 2 0 0 0 0 0 0', '5 0 0 0 0 0 0 0 0 2 0 1 1 0 0 1 0 0 0 0 0 1 0 0 0 0 0 3 0 0 1 0 1 0 2 3 0 0 0 0 0 0'}


process_div_curve(str_div='17 -10 -12 -10 -11 -11 -8 -5 -8 -4 -6 -5 -5 -8 -6 -3 -5 -5 -5 -5 -2 -6 -4 -1 -5 0 -4 -5 -3 -1 -2 -1 -2 -1 -3 -5 -2 -1 -4 0 0 0',str_curve='5 0 0 0 0 0 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 2 1 0 2 0 2 2 0 0 2 0 1 0 3 2 0 0 1 0 0 0',expect_nef=False)

for key1,val1 in div_curve_dict.items():
    process_div_curve(str_div=key1,str_curve=val1,expect_nef=False)

for curve1 in neg_curves:
    process_div_curve(str_curve=curve1,expect_nef=False)

for curve1 in nef_curves:
    process_div_curve(str_curve=curve1,expect_nef=True)


print("Entire program took",time.time()-start_time)


