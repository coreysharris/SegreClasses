newPackage(
     	"attempt",
	Version =>"0.2",
    	Date => "Nov 5, 2017",
    	Authors => {{Name => "Martin Helmer", 
		  Email => "martin.helmer@berkeley.edu", 
		  HomePage => "https://math.berkeley.edu/~mhelmer/"},
	         {Name => "Corey Harris", 
	       	  Email => "charris@math.fsu.edu", 
	          HomePage => "http://coreyharris.name"}
	      },
    	Headline => "Computes s(X,Y) in  A*(P^n)",
    	DebuggingMode => false,
	Reload => true
    	);

export{
   "sclass",
   "ChowRing",
   "MultiProjCoordRing",
   "isMultiHomogeneous",
   "Segre", 
   "makeMultiHom1",
   "makeMultiHom2",
   "HomMethod"

}


isMultiHomogeneous=method(TypicalValue=>Boolean);
isMultiHomogeneous Ideal:=I->(
    Igens:=flatten entries gens(I);
    d:=0;
    fmons:=0;
    for f in Igens do(
	fmons=flatten entries monomials(f);
	if length(fmons)>1 then(
	    d=degree(first(fmons));
	    for mon in fmons do(
		if degree(mon)!=d then(
		    <<"Input term below is not homogeneous with respect to the grading"<<endl;
		    <<f<<endl;
		    return false;
		    );
		);
	    
	    );
	);
    return true;
    
    );
isMultiHomogeneous RingElement:=f->(
    return isMultiHomogeneous(ideal(f));
    );
makeMultiHom1=method(TypicalValue=>Ideal);
makeMultiHom1 Ideal:=I->(
    R:=ring I;
    degs:=unique degrees R;
    n:=numgens(R)-length(degs);
    kk:=coefficientRing R;
    gensI:= delete(0_R,flatten sort entries gens I);
    exmon:=0;
    degI:= degrees I;
    m:=length unique degrees R;
    transDegI:= transpose degI;
    len:= length transDegI;
    maxDegs:= for i from 0 to len-1 list max transDegI_i;
    J:= for i from 1 to n list sum(gensI,g -> g*random(kk)*random(maxDegs-degree(g),R));
    return ideal J;
    );
makeMultiHom2=method(TypicalValue=>Ideal);
makeMultiHom2 Ideal:=I->(
    
    );

MultiProjCoordRing=method(TypicalValue=>Ring);
MultiProjCoordRing (Symbol,List):=(x,l)->(
    kk:=ZZ/32749;
    return MultiProjCoordRing(kk,x,l);
    );
MultiProjCoordRing (Ring,List):=(kk,l)->(
    x:=symbol x;
    return MultiProjCoordRing(kk,x,l);
    );
MultiProjCoordRing (List):=(l)->(
    x:=symbol x;
    kk:=ZZ/32749;
    return MultiProjCoordRing(kk,x,l);
    );
MultiProjCoordRing (Ring, Symbol,List):=(kk,x,l)->(
    if not isField(kk) then(
	<<"The coefficent ring must be a field, using the defalt feild kk=ZZ/32749"<<endl;
	kk=ZZ/32749;
	);
    totalDim:=sum(l);
    m:=length(l);
    numVars:=totalDim+m;
    degs:={};
    ind:=0;
    for n in l do (
	for i from 0 to n do(
	    degs=append(degs,OneAti(m,ind));
	    );
	ind=ind+1;
	);
    return kk[x_0..x_(numVars-1),Degrees=>degs];
    );

ChowRing=method(TypicalValue=>QuotientRing);
ChowRing (Ring):=(R)->(
    h:=symbol h;
    return ChowRing(R,h);
    );
ChowRing (Ring,Symbol):=(R,h)->(
    Rgens:=gens R;
    Rdegs:=degrees R;
    degd:=0;
    eqs:=0;
    ChDegs:=unique Rdegs;
    m:=length ChDegs;
    C:=ZZ[h_1..h_m,Degrees=>ChDegs];
    K:={};
    inds:={};
    rg:=0;
    ns:={};
    temp:=0;
    for d in ChDegs do(
	temp=0;
	for a in Rdegs do(
	    if d==a then temp=temp+1;
	    );
	ns=append(ns,temp);
	);
    
    for i from 0 to length(ChDegs)-1 do(
	K=append(K,C_(i)^(ns_i));
	);
    K=substitute(ideal K,C);
    A:=C/K;
    return A;
);

Segre=method(TypicalValue => RingElement,Options => {HomMethod=>1}); 
Segre (Ideal,Ideal) :=opts-> (I1,I2) -> ( 
    --print "start segre wrapper";
    A:=ChowRing(ring(I2));
    return Segre(I1,I2,A);
    );

Segre (Ideal,Ideal,QuotientRing) :=opts->(X,Y,A) -> (
    --print "start segre";
    if not isMultiHomogeneous(X) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHomogeneous(Y) then (print "the second ideal is not multi-homogenous, please correct this"; return 0;);
    Rx:=ring X;
    Ry:=ring Y;
    B:=flatten entries sort basis A;
    degs:=unique degrees Ry;
    --should work in any product of projective spaces
    --if length(degs)>2 then( print " too many projective spaces, Segre formula not implmented yet"; return 0;);
    tempId:={};
    PDl:={};
    for d in degs do(
	tempId={};
	for y in gens(Ry) do(
	    if degree(y)==d then(
		tempId=append(tempId,y);
		);
	    );
	PDl=append(PDl,ideal(tempId));
	);
    X=saturate(X,product(PDl));
    Y=saturate(Y,product(PDl));
    n:=numgens(Ry)-length(degs);
    --find the max multidegree, write it as a class alpha
    degX:= degrees (X+Y);
    transDegX:= transpose degX;
    len:= length transDegX;
    maxDegs:= for i from 0 to len-1 list max transDegX_i;
    deg1B:={};
    for w in B do if sum(degree(w))==1 then deg1B=append(deg1B,w);
    m:=length degs;
    alpha:=sum(length deg1B,i->(basis(OneAti(m,i),A))_0_0*maxDegs_i); 
    zdim:=0;
    for b in B do(
	if sum(flatten(exponents(b)))==n then zdim=b;
	);
    seg:=0;
     
    --h:=A_0;
    -- Y subvariety of PPn
    -- X closed subscheme of Y
    --Find dimension of Y
    kk:=coefficientRing Ry;
    t:=symbol t;
    R:=kk[gens Ry,t];
    --n is (projective) dimension of ambient space
    --n:=numgens(Ry) -1;
    --find gb's
    gbX := groebnerBasis(X+Y, Strategy=>"MGB");
    gbY := groebnerBasis(Y, Strategy=>"MGB");
    codimX := codim ideal leadTerm gbX;
    codimY:= codim ideal leadTerm gbY;
    dimX := n-codimX;
    dimY:= n-codimY;
    --Degree only depends on the leading monomials of a GB
    --degY:=degree monomialIdeal gbY;
    c:={};
    v:=0;
    Ls:=0;
    ve:=0;
    ZeroDimGB:=0;
    LA:=0;
    clY:=0;
    for p in PDl do (
	LA=LA+ideal(1-sum(numgens(p),i->random(kk)*p_i));
	);
    --print "start compute class Y";
    for w in B do if sum(flatten(exponents(w)))==codimY then c=append(c,w);
    for w in c do(
	Ls=0;
	v=zdim//w;
	    ve=flatten exponents(v);
	    for i from 0 to length(ve)-1 do(
	    	if ve_i!=0 then (
		    Ls=Ls+sum(ve_i,j->ideal(random(OneAti(m,i),Ry)));
		    );
	    	);
	    ZeroDimGB=ideal groebnerBasis(ideal(gbY)+Ls+LA, Strategy=>"F4");
	    clY=clY+(numColumns basis(cokernel leadTerm ZeroDimGB))*w;
	    
	);
    --<<"codim LA= "<<codim(LA)<<", LA= "<<LA<<endl;
    <<"[Y]= "<<clY<<<<", alpha= "<<alpha<<endl;
    --print "end compute class Y";
    --degY*h^(n-dimY);
    -- V \subset |O(d)| is the linear system on Y for which X is the base scheme
    -- in reality, it's the largest degree among the generators of (X + Y)
    --d := first degree( (gens homogenate(X+Y))_(0,0) );
    W:=X+Y;
    Wg:=0;
    G:=0;
    pd:=0;
    EqT:=0;
    c={};
    projectiveDegreesList := {};
    deltaDegreesList := {};
    --print "start main loop";
    --<<"dimY= "<<dimY<<endl;
    
    for i from 0 to dimX do (
	c={};
    	for w in B do if sum(flatten(exponents(w)))==n-i then c=append(c,w);
	for w in c do(
	    Ls=ideal 0_Ry;
	    LA=ideal 0_Ry;
            --pd := projDegree(homogenate(X+Y+L),Y+L);
	    v=zdim//w;
	    ve=flatten exponents(v);
	    for i from 0 to length(ve)-1 do(
	    	if ve_i!=0 then (
		    Ls=Ls+sum(ve_i,j->ideal(random(OneAti(m,i),Ry)));
		    );
	    	);
	    for p in PDl do (
	    	LA=LA+sub(ideal(1-sum(numgens(p),i->random(kk)*p_i)),Ry);
	    	);
	    --<<"w= "<<w<<",Ls= "<<Ls<<<<",LA= "<<(LA)<<endl;
	    EqT=ideal( sum((numgens X),j->(1-t*random(kk)*substitute(X_j,R))));
	    if opts.HomMethod ==2 then (Wg=flatten entries gens homogenate(W+Ls);) else (Wg=flatten entries gens makeMultiHom1(W+Ls););
	    --Wg=flatten entries gens homogenate(W+Ls);
	    G=ideal(for j from 1 to dimY-i list sum(Wg,g->random(kk)*g));
	    --print "start gb";
	    --print(toString(sub(Y+Ls+G+LA,R)+EqT));
	    ZeroDimGB=groebnerBasis(sub(Y+Ls+G+LA,R)+EqT, Strategy=>"F4");
	    --<<"dim= "<<dim(ideal(ZeroDimGB))<<", codim G= "<<codim(G)<<<<", codim Ls= "<<codim(Ls)<<endl;
            --<<"G= "<<G<<",Ls= "<<Ls<<<<",LA= "<<(LA)<<endl;
	    pd=numColumns basis(cokernel leadTerm ZeroDimGB);
	    --<<"w= "<<w<<", pd= "<<pd<<endl;
            projectiveDegreesList = append(projectiveDegreesList,pd*w);
	    );
	);
     <<"Projective degrees= "<<projectiveDegreesList<<endl;
    Gam:=sum(projectiveDegreesList);
    --SumOverList:={};
    --for w in B do if sum(flatten(exponents(w)))>=n-dimX then SumOverList=append(SumOverList,w);
    SegClass:=0_A;
    temp7:=0;
    temp9:=0;
    RHS:=sum(0..dimX,i->alpha^(dimY-i)*clY)-Gam;--sum(SumOverList,w->w*alpha^(dimY-sum(flatten(exponents(zdim//w)))));
    for i from 0 to dimX do(
	c={};
	for w in B do if sum(flatten(exponents(w)))==n-(dimX-i) then c=append(c,w);
	for w in c do(
	    temp9=(zdim//w);
	    temp7=RHS_(w)-(temp9*(1+alpha)^(dimY-sum(flatten(exponents(temp9))))*SegClass)_(zdim);
	    SegClass=SegClass+temp7*w;
	    --<<"w= "<<w<<", SegClass= "<<SegClass<<" coeff= "<<(1+alpha)^(dimY-sum(flatten(exponents(temp9))))<<endl;
	    );	
	);
    <<"s(X,Y)= "<<SegClass<<endl;
    use Ry;
    return SegClass;
);

sclass=method(TypicalValue => RingElement); 
sclass (Ideal,Ideal) := (I1,I2) -> ( 
    A:=ChowRing(ring(I2));
    return sclass(I1,I2,A);
    );

sclass (Ideal,Ideal,QuotientRing) := (X,Y,A) -> (
    Rx:=ring X;
    Ry:=ring Y; 
    h:=A_0;
    -- Y subvariety of PPn
    -- X closed subscheme of Y
    --Find dimension of Y
    kk:=coefficientRing Ry;
    t:=symbol t;
    R:=kk[gens Ry,t];
    --n is (projective) dimension of ambient space
    n:=numgens(Ry) -1;
    --find gb's
    gbX := groebnerBasis(X+Y, Strategy=>"MGB");
    gbY := groebnerBasis(Y, Strategy=>"MGB");
    dimX := n-codim ideal leadTerm gbX;
    dimY:= n-codim ideal leadTerm gbY;
    --Degree only depends on the leading monomials of a GB
    degY:=degree monomialIdeal gbY;
    clY:=degY*h^(n-dimY);
    
    -- V \subset |O(d)| is the linear system on Y for which X is the base scheme
    -- in reality, it's the largest degree among the generators of (X + Y)
    d := first degree( (gens homogenate(X+Y))_(0,0) );
    W:=X+Y;
    Wg:=0;
    G:=0;
    pd:=0;
    LA:=0;
    EqT:=0;
    ZeroDimGB:=0;
    projectiveDegreesList := {};
    deltaDegreesList := {};
    L := ideal sub(0,ring X);
    for i from 0 to dimX do (
        --pd := projDegree(homogenate(X+Y+L),Y+L);
	LA=sub(ideal(1-sum(numgens Ry,j->random(kk)*(gens(Ry))_j)),R);
	EqT=ideal( sum((numgens X),i->(1-t*random(kk)*substitute(X_i,R))));
	Wg=flatten entries gens homogenate(W+L);
	G=ideal(for j from 1 to dimY-i list sum(Wg,g->random(kk)*g));
	ZeroDimGB=groebnerBasis(sub(Y+L+G,R)+LA+EqT, Strategy=>"F4");
        pd=numColumns basis(cokernel leadTerm ZeroDimGB);
        projectiveDegreesList = append(projectiveDegreesList,pd*h^(n-i));
        -- the simple formula for converting deltaDegreesList to i_*(s(X,Y))
        -- is given in [Har17, Proposition 5]
        deltaDegreesList = append(deltaDegreesList, (d*h)^(dimY - i) *clY - pd*h^(n-i));
        L = L + ideal random(1,Ry);
	);
    --segreList:={};
    --temp:=0;
    --for i from 0 to dimX do(
	--temp=for j from 0 to i-1 list binomial(-dimX+i,j+1)*d^(j+1);
	--<<"delta val= "<<delta_(dimX-i)<<", binom= "<<sum(i,j->binomial(dimY-dimX+i,j+1)*d^(j+1)*segreList_(i-j-1))<<endl;
--	segreList=prepend(deltaDegreesList_(dimX-i)-(sum(i,j->binomial(dimY-dimX+i,j+1)*d^(j+1)*segreList_(i-j-1)) ),segreList);
--	); 
--    segre:=sum(length(segreList),i->segreList_i*h^(n-i));
    --<<"Segre= "<<segre<<endl;
    use Ry;
    return (projectiveDegreesList,deltaDegreesList)
)

projDegree = (X,Y) -> (
    hyperplanePullbacks := for i from 1 to dim variety Y list (
        ideal (sum apply(flatten entries gens X, g -> random(0,ring X)*g))
    );
    -- I is a set of points in PPn
    G := sum hyperplanePullbacks;
    I := saturate(Y + G, X);
    return degree I
)

----------------------------
-- utility functions
----------------------------

homogenated = I -> (
    -- get a list of degrees of the generators of I and take the max
    gns := flatten entries gens I;
    degs := apply(gns, g -> (degree g)#0);
    maxDeg := max(degs);

    -- test whether all degrees attain the max
    return all(degs, d -> d == maxDeg);
)

-- make all generators of X have the same degree
homogenate = I -> (
    -- no need to do all this work if the generators are already of same degree
    if (homogenated I) then return I;

    -- get list of generators and take max degree
    gns := flatten entries gens I;
    maxDeg := max(apply(gns, g -> (degree g)#0));

    -- split the list into sublists by degree
    -- e.g. { z, xy2, x2y, x3+y3 } -> { {}, {z}, {}, {xy2, x2y}, {x3+y3}  }
    gLists := for i from 0 to maxDeg list (
        select(gns, g -> (degree g)#0 == i)
    );

    J := ideal ( vars ring I ); 

    gs := for i to ( (length gLists)-1) list (
        -- the ith list in gLists is the set of degree i generators
        flatten entries mingens (
            J^(maxDeg - i) * sub(ideal(gLists#i), ring I)
        ) 
    );
    return trim ideal (flatten gs);
)

OneAti=(dl,i)->(
    vec:={};
    for j from 0 to dl-1 do(
	if j==i then vec=append(vec,1) else vec=append(vec,0);
	);
    return vec;
    )

irrell=R->(    
    Rgens:=gens R;
    Rdegs:=degrees R;
    bloks:=unique Rdegs;
    irId:=ideal 1_R;
    elList:={};
    for a in bloks do(
	elList={};
	for r in Rgens do(
	    if degree(r)==a then(
		elList=append(elList,r);
		);
	    );
	irId=irId*ideal(elList)
	
	);
    return irId;
    )

TEST ///
{*  
    restart
    needsPackage "attempt"
*} 
  
restart
needsPackage "attempt"
needsPackage "FMPIntersectionTheory"
PP3 = QQ[w,x,y,z]
Y = ideal(x*y-z*w)
X = ideal(x)
segreClass(X,Y)
--({2, 2}, {6, 2})
Segre(X,Y)
X = ideal(x,z)
segreClass(X,Y)
-- ({4, 3}, {4, 1})
R=MultiProjCoordRing({2,3})
x=gens(R)
I=ideal(x_0*x_1*x_5-x_2^2*x_6)
J=ideal(x_0)
Segre(J,I);


restart
-- test in a normal projective space
needsPackage "attempt"
needsPackage "FMPIntersectionTheory"
PP3 = QQ[x,y,z,t]
Y = ideal "xy-zt"
X = ideal random(4,PP3)
segreClass(X,Y)
Segre(X,Y) 



restart
-- point on a line
needsPackage "attempt"
R = MultiProjCoordRing({1,1})
x=gens R
D=ideal(x_0*x_3-x_1*x_2)
Segre(ideal(x_0-x_1), D)
-- s(PP0,PP1) = [PP0]

-- union of coordinate axes in PP3 (diagonal)
needsPackage "attempt"
R = MultiProjCoordRing({3,3})
x = gens(R)
D = minors(2,matrix{{x_0..x_3},{x_4..x_7}})
X = ideal(x_0*x_1,x_1*x_2,x_0*x_2)
Segre(X,D)
-- s(axes,PP3) = 3[PP1] - 10[PP0] ... I think this means 3 *("both" PP1's)
-- i.e. h^3h_2^2 and h^2h_2^3

restart
needsPackage "attempt"
R = ZZ/32749[x,y,z,t]
PP3xPP3 = MultiProjCoordRing({3,3})
m1 = map(PP3xPP3,R,take(gens PP3xPP3,4))
m2 = map(PP3xPP3,R,drop(gens PP3xPP3,4))
f = ideal "x(x2-2xy+zt) + y(x2-3yt+z2+3t2-3tz+xy)"
h = ideal "x(x2-7y2-zt) + y(3x2-5yt)"
X = m1(f)
Y = m2(h)
D = minors(2,matrix{take(gens PP3xPP3,4),drop(gens PP3xPP3,4)})
X+Y
Segre(D, X+Y)
x=gens R
J=ideal(x_0^3-x_0^2*x_1+x_0*x_1^2+x_1*x_2^2-3*x_1^2*x_3+x_0*x_2*x_3-3*x_1*x_2*x_3+3*x_1*x_3^2,x_4^3+3*x_4^2*x_5-7*x_4*x_5^2-5*x_5^2*x_7-x_4*x_6*x_7,-11544*x_0^3*x_4^3+15636*x_0^2*x_1*x_4^3-10584*x_0*x_1^2*x_4^3+9680*x_1^3*x_4^3+11484*x_0^2*x_2*x_4^3+5953*x_0*x_1*x_2*x_4^3-8537*x_1^2*x_2*x_4^3+14875*x_0*x_2^2*x_4^3+15064*x_1*x_2^2*x_4^3-3670*x_2^3*x_4^3-9816*x_0^2*x_3*x_4^3-2206*x_0*x_1*x_3*x_4^3-6646*x_1^2*x_3*x_4^3-14641*x_0*x_2*x_3*x_4^3-6861*x_1*x_2*x_3*x_4^3+8406*x_2^2*x_3*x_4^3-1533*x_0*x_3^2*x_4^3-15596*x_1*x_3^2*x_4^3-1672*x_2*x_3^2*x_4^3+12586*x_3^3*x_4^3-14130*x_0^3*x_4^2*x_5-5691*x_0^2*x_1*x_4^2*x_5+8350*x_0*x_1^2*x_4^2*x_5+13981*x_1^3*x_4^2*x_5+15955*x_0^2*x_2*x_4^2*x_5+4969*x_0*x_1*x_2*x_4^2*x_5+6368*x_1^2*x_2*x_4^2*x_5+4718*x_0*x_2^2*x_4^2*x_5+2601*x_1*x_2^2*x_4^2*x_5-16251*x_2^3*x_4^2*x_5-940*x_0^2*x_3*x_4^2*x_5+4684*x_0*x_1*x_3*x_4^2*x_5-12414*x_1^2*x_3*x_4^2*x_5+8794*x_0*x_2*x_3*x_4^2*x_5-4117*x_1*x_2*x_3*x_4^2*x_5+3580*x_2^2*x_3*x_4^2*x_5-5130*x_0*x_3^2*x_4^2*x_5-7550*x_1*x_3^2*x_4^2*x_5-5246*x_2*x_3^2*x_4^2*x_5+12426*x_3^3*x_4^2*x_5-14759*x_0^3*x_4*x_5^2+14226*x_0^2*x_1*x_4*x_5^2+12551*x_0*x_1^2*x_4*x_5^2-6896*x_1^3*x_4*x_5^2-1730*x_0^2*x_2*x_4*x_5^2-3608*x_0*x_1*x_2*x_4*x_5^2+10572*x_1^2*x_2*x_4*x_5^2-11719*x_0*x_2^2*x_4*x_5^2-4100*x_1*x_2^2*x_4*x_5^2-485*x_2^3*x_4*x_5^2-7926*x_0^2*x_3*x_4*x_5^2-8489*x_0*x_1*x_3*x_4*x_5^2+11842*x_1^2*x_3*x_4*x_5^2-8268*x_0*x_2*x_3*x_4*x_5^2+9533*x_1*x_2*x_3*x_4*x_5^2-6877*x_2^2*x_3*x_4*x_5^2-11998*x_0*x_3^2*x_4*x_5^2-15360*x_1*x_3^2*x_4*x_5^2+7949*x_2*x_3^2*x_4*x_5^2+6386*x_3^3*x_4*x_5^2+3496*x_0^3*x_5^3+13886*x_0^2*x_1*x_5^3-7049*x_0*x_1^2*x_5^3+11467*x_0^2*x_2*x_5^3-14841*x_0*x_1*x_2*x_5^3-3591*x_1^2*x_2*x_5^3+7533*x_0*x_2^2*x_5^3+15076*x_1*x_2^2*x_5^3+15322*x_2^3*x_5^3+12892*x_0^2*x_3*x_5^3+11148*x_0*x_1*x_3*x_5^3+16237*x_1^2*x_3*x_5^3-2538*x_0*x_2*x_3*x_5^3-9105*x_1*x_2*x_3*x_5^3+7640*x_2^2*x_3*x_5^3-8983*x_0*x_3^2*x_5^3+8247*x_1*x_3^2*x_5^3+15328*x_2*x_3^2*x_5^3+15624*x_3^3*x_5^3-14801*x_0^3*x_4^2*x_6-14637*x_0^2*x_1*x_4^2*x_6+7153*x_0*x_1^2*x_4^2*x_6+12696*x_1^3*x_4^2*x_6+9708*x_0^2*x_2*x_4^2*x_6-14892*x_0*x_1*x_2*x_4^2*x_6+3099*x_1^2*x_2*x_4^2*x_6+12052*x_0*x_2^2*x_4^2*x_6+14770*x_1*x_2^2*x_4^2*x_6-14904*x_2^3*x_4^2*x_6+3050*x_0^2*x_3*x_4^2*x_6-4836*x_0*x_1*x_3*x_4^2*x_6-6268*x_1^2*x_3*x_4^2*x_6-3831*x_0*x_2*x_3*x_4^2*x_6+15635*x_1*x_2*x_3*x_4^2*x_6-14798*x_2^2*x_3*x_4^2*x_6+15817*x_0*x_3^2*x_4^2*x_6-11558*x_1*x_3^2*x_4^2*x_6-11322*x_2*x_3^2*x_4^2*x_6+13036*x_3^3*x_4^2*x_6+10681*x_0^3*x_4*x_5*x_6+1539*x_0^2*x_1*x_4*x_5*x_6+6994*x_0*x_1^2*x_4*x_5*x_6+10376*x_1^3*x_4*x_5*x_6+12059*x_0^2*x_2*x_4*x_5*x_6-5678*x_0*x_1*x_2*x_4*x_5*x_6+6066*x_1^2*x_2*x_4*x_5*x_6+12399*x_0*x_2^2*x_4*x_5*x_6+10809*x_1*x_2^2*x_4*x_5*x_6+15510*x_2^3*x_4*x_5*x_6+2740*x_0^2*x_3*x_4*x_5*x_6-11859*x_0*x_1*x_3*x_4*x_5*x_6-10111*x_1^2*x_3*x_4*x_5*x_6-2455*x_0*x_2*x_3*x_4*x_5*x_6+6077*x_1*x_2*x_3*x_4*x_5*x_6-14549*x_2^2*x_3*x_4*x_5*x_6-13817*x_0*x_3^2*x_4*x_5*x_6+604*x_1*x_3^2*x_4*x_5*x_6-15218*x_2*x_3^2*x_4*x_5*x_6+10683*x_3^3*x_4*x_5*x_6+257*x_0^3*x_5^2*x_6-10605*x_0^2*x_1*x_5^2*x_6-12651*x_0*x_1^2*x_5^2*x_6+3591*x_1^3*x_5^2*x_6+8189*x_0^2*x_2*x_5^2*x_6-14005*x_0*x_1*x_2*x_5^2*x_6+185*x_1^2*x_2*x_5^2*x_6+14434*x_0*x_2^2*x_5^2*x_6+1169*x_1*x_2^2*x_5^2*x_6+10473*x_2^3*x_5^2*x_6-14775*x_0^2*x_3*x_5^2*x_6-13841*x_0*x_1*x_3*x_5^2*x_6-14743*x_1^2*x_3*x_5^2*x_6-5287*x_0*x_2*x_3*x_5^2*x_6+7000*x_1*x_2*x_3*x_5^2*x_6+15712*x_2^2*x_3*x_5^2*x_6-6162*x_0*x_3^2*x_5^2*x_6+512*x_1*x_3^2*x_5^2*x_6+11854*x_2*x_3^2*x_5^2*x_6-7554*x_3^3*x_5^2*x_6-10621*x_0^3*x_4*x_6^2+8663*x_0^2*x_1*x_4*x_6^2+16301*x_0*x_1^2*x_4*x_6^2-15515*x_1^3*x_4*x_6^2-10805*x_0^2*x_2*x_4*x_6^2+2401*x_0*x_1*x_2*x_4*x_6^2+5018*x_1^2*x_2*x_4*x_6^2-10869*x_0*x_2^2*x_4*x_6^2+15150*x_1*x_2^2*x_4*x_6^2+8854*x_2^3*x_4*x_6^2+15577*x_0^2*x_3*x_4*x_6^2-15133*x_0*x_1*x_3*x_4*x_6^2-3883*x_1^2*x_3*x_4*x_6^2-6348*x_0*x_2*x_3*x_4*x_6^2-5706*x_1*x_2*x_3*x_4*x_6^2-3573*x_2^2*x_3*x_4*x_6^2+2189*x_0*x_3^2*x_4*x_6^2-13715*x_1*x_3^2*x_4*x_6^2+8869*x_2*x_3^2*x_4*x_6^2+12518*x_3^3*x_4*x_6^2-5528*x_0^3*x_5*x_6^2+705*x_0^2*x_1*x_5*x_6^2-3734*x_0*x_1^2*x_5*x_6^2+10549*x_1^3*x_5*x_6^2-7113*x_0^2*x_2*x_5*x_6^2+11787*x_0*x_1*x_2*x_5*x_6^2-10479*x_1^2*x_2*x_5*x_6^2+11885*x_0*x_2^2*x_5*x_6^2+15815*x_1*x_2^2*x_5*x_6^2-15243*x_2^3*x_5*x_6^2-8726*x_0^2*x_3*x_5*x_6^2-7091*x_0*x_1*x_3*x_5*x_6^2+2424*x_1^2*x_3*x_5*x_6^2+1191*x_0*x_2*x_3*x_5*x_6^2+6766*x_1*x_2*x_3*x_5*x_6^2-6117*x_2^2*x_3*x_5*x_6^2-6044*x_0*x_3^2*x_5*x_6^2-1257*x_1*x_3^2*x_5*x_6^2-4143*x_2*x_3^2*x_5*x_6^2+6424*x_3^3*x_5*x_6^2-308*x_0^3*x_6^3-14534*x_0^2*x_1*x_6^3-14127*x_0*x_1^2*x_6^3-5325*x_1^3*x_6^3-6976*x_0^2*x_2*x_6^3-14844*x_0*x_1*x_2*x_6^3-5199*x_1^2*x_2*x_6^3-8854*x_0*x_2^2*x_6^3-8473*x_1*x_2^2*x_6^3-15362*x_0^2*x_3*x_6^3-8571*x_0*x_1*x_3*x_6^3-14685*x_1^2*x_3*x_6^3+13272*x_0*x_2*x_3*x_6^3+7470*x_1*x_2*x_3*x_6^3+520*x_2^2*x_3*x_6^3-6624*x_0*x_3^2*x_6^3-10031*x_1*x_3^2*x_6^3+11327*x_2*x_3^2*x_6^3+8933*x_3^3*x_6^3-14108*x_0^3*x_4^2*x_7-7334*x_0^2*x_1*x_4^2*x_7+99*x_0*x_1^2*x_4^2*x_7-4252*x_1^3*x_4^2*x_7+7319*x_0^2*x_2*x_4^2*x_7+3585*x_0*x_1*x_2*x_4^2*x_7-10534*x_1^2*x_2*x_4^2*x_7+5118*x_0*x_2^2*x_4^2*x_7-9970*x_1*x_2^2*x_4^2*x_7-7623*x_2^3*x_4^2*x_7-14441*x_0^2*x_3*x_4^2*x_7+7254*x_0*x_1*x_3*x_4^2*x_7-6005*x_1^2*x_3*x_4^2*x_7+3815*x_0*x_2*x_3*x_4^2*x_7+14394*x_1*x_2*x_3*x_4^2*x_7-1491*x_2^2*x_3*x_4^2*x_7+13261*x_0*x_3^2*x_4^2*x_7-4759*x_1*x_3^2*x_4^2*x_7+15719*x_2*x_3^2*x_4^2*x_7+4633*x_3^3*x_4^2*x_7+6691*x_0^3*x_4*x_5*x_7+11744*x_0^2*x_1*x_4*x_5*x_7-9682*x_0*x_1^2*x_4*x_5*x_7-7082*x_1^3*x_4*x_5*x_7+7380*x_0^2*x_2*x_4*x_5*x_7+15589*x_0*x_1*x_2*x_4*x_5*x_7+7300*x_1^2*x_2*x_4*x_5*x_7+6016*x_0*x_2^2*x_4*x_5*x_7+5451*x_1*x_2^2*x_4*x_5*x_7-253*x_2^3*x_4*x_5*x_7-14409*x_0^2*x_3*x_4*x_5*x_7+7578*x_0*x_1*x_3*x_4*x_5*x_7-4793*x_1^2*x_3*x_4*x_5*x_7+2997*x_0*x_2*x_3*x_4*x_5*x_7+1562*x_1*x_2*x_3*x_4*x_5*x_7-2842*x_2^2*x_3*x_4*x_5*x_7-10125*x_0*x_3^2*x_4*x_5*x_7+5797*x_1*x_3^2*x_4*x_5*x_7+6563*x_2*x_3^2*x_4*x_5*x_7-3101*x_3^3*x_4*x_5*x_7+9770*x_0^3*x_5^2*x_7-11440*x_0^2*x_1*x_5^2*x_7+2161*x_0*x_1^2*x_5^2*x_7+13611*x_1^3*x_5^2*x_7-14253*x_0^2*x_2*x_5^2*x_7-2371*x_0*x_1*x_2*x_5^2*x_7+16173*x_1^2*x_2*x_5^2*x_7+7501*x_0*x_2^2*x_5^2*x_7-11856*x_1*x_2^2*x_5^2*x_7+7744*x_2^3*x_5^2*x_7+12102*x_0^2*x_3*x_5^2*x_7-10089*x_0*x_1*x_3*x_5^2*x_7+10628*x_1^2*x_3*x_5^2*x_7+8522*x_0*x_2*x_3*x_5^2*x_7-12215*x_1*x_2*x_3*x_5^2*x_7+10372*x_2^2*x_3*x_5^2*x_7-587*x_0*x_3^2*x_5^2*x_7-938*x_1*x_3^2*x_5^2*x_7-5299*x_2*x_3^2*x_5^2*x_7+6738*x_3^3*x_5^2*x_7-4167*x_0^3*x_4*x_6*x_7+8220*x_0^2*x_1*x_4*x_6*x_7+14603*x_0*x_1^2*x_4*x_6*x_7+13256*x_1^3*x_4*x_6*x_7-11583*x_0^2*x_2*x_4*x_6*x_7-7199*x_0*x_1*x_2*x_4*x_6*x_7+10867*x_1^2*x_2*x_4*x_6*x_7+14658*x_0*x_2^2*x_4*x_6*x_7-1537*x_1*x_2^2*x_4*x_6*x_7-4305*x_2^3*x_4*x_6*x_7-836*x_0^2*x_3*x_4*x_6*x_7-15380*x_0*x_1*x_3*x_4*x_6*x_7+6972*x_1^2*x_3*x_4*x_6*x_7-16348*x_0*x_2*x_3*x_4*x_6*x_7-9169*x_1*x_2*x_3*x_4*x_6*x_7-3603*x_2^2*x_3*x_4*x_6*x_7-5158*x_0*x_3^2*x_4*x_6*x_7+10336*x_1*x_3^2*x_4*x_6*x_7+15191*x_2*x_3^2*x_4*x_6*x_7-13809*x_3^3*x_4*x_6*x_7-1153*x_0^3*x_5*x_6*x_7-14042*x_0^2*x_1*x_5*x_6*x_7-2105*x_0*x_1^2*x_5*x_6*x_7-11483*x_1^3*x_5*x_6*x_7-14594*x_0^2*x_2*x_5*x_6*x_7+11520*x_0*x_1*x_2*x_5*x_6*x_7+7989*x_1^2*x_2*x_5*x_6*x_7-14748*x_0*x_2^2*x_5*x_6*x_7-13516*x_1*x_2^2*x_5*x_6*x_7+16308*x_2^3*x_5*x_6*x_7-3142*x_0^2*x_3*x_5*x_6*x_7-5731*x_0*x_1*x_3*x_5*x_6*x_7-5479*x_1^2*x_3*x_5*x_6*x_7-13930*x_0*x_2*x_3*x_5*x_6*x_7-5016*x_1*x_2*x_3*x_5*x_6*x_7-11626*x_2^2*x_3*x_5*x_6*x_7-10125*x_0*x_3^2*x_5*x_6*x_7+275*x_1*x_3^2*x_5*x_6*x_7+3184*x_2*x_3^2*x_5*x_6*x_7-8425*x_3^3*x_5*x_6*x_7-3379*x_0^3*x_6^2*x_7-16156*x_0^2*x_1*x_6^2*x_7+10126*x_0*x_1^2*x_6^2*x_7-10274*x_1^3*x_6^2*x_7+5415*x_0^2*x_2*x_6^2*x_7-2944*x_0*x_1*x_2*x_6^2*x_7-9228*x_1^2*x_2*x_6^2*x_7+15403*x_0*x_2^2*x_6^2*x_7+12313*x_1*x_2^2*x_6^2*x_7-520*x_2^3*x_6^2*x_7-10737*x_0^2*x_3*x_6^2*x_7+12229*x_0*x_1*x_3*x_6^2*x_7+12873*x_1^2*x_3*x_6^2*x_7-16020*x_0*x_2*x_3*x_6^2*x_7+15544*x_1*x_2*x_3*x_6^2*x_7-8713*x_2^2*x_3*x_6^2*x_7+10096*x_0*x_3^2*x_6^2*x_7+10933*x_1*x_3^2*x_6^2*x_7+9881*x_2*x_3^2*x_6^2*x_7-1196*x_3^3*x_6^2*x_7-11400*x_0^3*x_4*x_7^2-11315*x_0^2*x_1*x_4*x_7^2+1174*x_0*x_1^2*x_4*x_7^2+12384*x_1^3*x_4*x_7^2+7935*x_0^2*x_2*x_4*x_7^2-3209*x_0*x_1*x_2*x_4*x_7^2-16281*x_1^2*x_2*x_4*x_7^2+13645*x_0*x_2^2*x_4*x_7^2-10059*x_1*x_2^2*x_4*x_7^2+14577*x_2^3*x_4*x_7^2+15624*x_0^2*x_3*x_4*x_7^2-6121*x_0*x_1*x_3*x_4*x_7^2+2598*x_1^2*x_3*x_4*x_7^2-9035*x_0*x_2*x_3*x_4*x_7^2-2495*x_1*x_2*x_3*x_4*x_7^2+5162*x_2^2*x_3*x_4*x_7^2+3719*x_0*x_3^2*x_4*x_7^2+12621*x_1*x_3^2*x_4*x_7^2-2512*x_2*x_3^2*x_4*x_7^2-13466*x_3^3*x_4*x_7^2-1461*x_0^3*x_5*x_7^2+5577*x_0^2*x_1*x_5*x_7^2-4398*x_0*x_1^2*x_5*x_7^2+613*x_1^3*x_5*x_7^2-8227*x_0^2*x_2*x_5*x_7^2-9093*x_0*x_1*x_2*x_5*x_7^2-10329*x_1^2*x_2*x_5*x_7^2+4128*x_0*x_2^2*x_5*x_7^2+10531*x_1*x_2^2*x_5*x_7^2+1425*x_2^3*x_5*x_7^2-13490*x_0^2*x_3*x_5*x_7^2-15946*x_0*x_1*x_3*x_5*x_7^2-698*x_1^2*x_3*x_5*x_7^2-10048*x_0*x_2*x_3*x_5*x_7^2-5629*x_1*x_2*x_3*x_5*x_7^2-11774*x_2^2*x_3*x_5*x_7^2+12858*x_0*x_3^2*x_5*x_7^2-7896*x_1*x_3^2*x_5*x_7^2-4247*x_2*x_3^2*x_5*x_7^2+14907*x_3^3*x_5*x_7^2-2325*x_0^3*x_6*x_7^2-927*x_0^2*x_1*x_6*x_7^2-12914*x_0*x_1^2*x_6*x_7^2+3791*x_1^3*x_6*x_7^2+13173*x_0^2*x_2*x_6*x_7^2+11530*x_0*x_1*x_2*x_6*x_7^2+12670*x_1^2*x_2*x_6*x_7^2-14544*x_0*x_2^2*x_6*x_7^2+6005*x_1*x_2^2*x_6*x_7^2-2614*x_2^3*x_6*x_7^2+7633*x_0^2*x_3*x_6*x_7^2+4965*x_0*x_1*x_3*x_6*x_7^2+1809*x_1^2*x_3*x_6*x_7^2-2630*x_0*x_2*x_3*x_6*x_7^2-10096*x_1*x_2*x_3*x_6*x_7^2+12991*x_2^2*x_3*x_6*x_7^2+15881*x_0*x_3^2*x_6*x_7^2-11312*x_1*x_3^2*x_6*x_7^2+5486*x_2*x_3^2*x_6*x_7^2+14549*x_3^3*x_6*x_7^2+3574*x_0^3*x_7^3-7531*x_0^2*x_1*x_7^3+9589*x_0*x_1^2*x_7^3-5190*x_1^3*x_7^3-12139*x_0^2*x_2*x_7^3-5834*x_0*x_1*x_2*x_7^3-2650*x_1^2*x_2*x_7^3+6388*x_0*x_2^2*x_7^3+16164*x_1*x_2^2*x_7^3+944*x_2^3*x_7^3-8352*x_0^2*x_3*x_7^3-15606*x_0*x_1*x_3*x_7^3-2498*x_1^2*x_3*x_7^3-844*x_0*x_2*x_3*x_7^3+5611*x_1*x_2*x_3*x_7^3-4290*x_2^2*x_3*x_7^3+13466*x_0*x_3^2*x_7^3+1611*x_1*x_3^2*x_7^3-14549*x_2*x_3^2*x_7^3,-14256*x_0^3*x_4^3+12310*x_0^2*x_1*x_4^3-10568*x_0*x_1^2*x_4^3+3740*x_1^3*x_4^3-11549*x_0^2*x_2*x_4^3-10321*x_0*x_1*x_2*x_4^3-13059*x_1^2*x_2*x_4^3-7*x_0*x_2^2*x_4^3-1891*x_1*x_2^2*x_4^3-3736*x_2^3*x_4^3-7565*x_0^2*x_3*x_4^3-15176*x_0*x_1*x_3*x_4^3-4804*x_1^2*x_3*x_4^3-15005*x_0*x_2*x_3*x_4^3-15722*x_1*x_2*x_3*x_4^3+13305*x_2^2*x_3*x_4^3-9601*x_0*x_3^2*x_4^3+3475*x_1*x_3^2*x_4^3-1276*x_2*x_3^2*x_4^3+5358*x_3^3*x_4^3+2241*x_0^3*x_4^2*x_5-8698*x_0^2*x_1*x_4^2*x_5+5678*x_0*x_1^2*x_4^2*x_5+6111*x_1^3*x_4^2*x_5+3264*x_0^2*x_2*x_4^2*x_5-12611*x_0*x_1*x_2*x_4^2*x_5-3525*x_1^2*x_2*x_4^2*x_5+76*x_0*x_2^2*x_4^2*x_5+1317*x_1*x_2^2*x_4^2*x_5+6537*x_2^3*x_4^2*x_5+12742*x_0^2*x_3*x_4^2*x_5+13027*x_0*x_1*x_3*x_4^2*x_5+2279*x_1^2*x_3*x_4^2*x_5-14536*x_0*x_2*x_3*x_4^2*x_5+14697*x_1*x_2*x_3*x_4^2*x_5+10416*x_2^2*x_3*x_4^2*x_5+15675*x_0*x_3^2*x_4^2*x_5-4810*x_1*x_3^2*x_4^2*x_5+699*x_2*x_3^2*x_4^2*x_5-1275*x_3^3*x_4^2*x_5+16295*x_0^3*x_4*x_5^2+9444*x_0^2*x_1*x_4*x_5^2-10782*x_0*x_1^2*x_4*x_5^2-11578*x_1^3*x_4*x_5^2-10252*x_0^2*x_2*x_4*x_5^2+7921*x_0*x_1*x_2*x_4*x_5^2-13357*x_1^2*x_2*x_4*x_5^2-8854*x_0*x_2^2*x_4*x_5^2+5230*x_1*x_2^2*x_4*x_5^2+8687*x_2^3*x_4*x_5^2-14252*x_0^2*x_3*x_4*x_5^2-12105*x_0*x_1*x_3*x_4*x_5^2+7663*x_1^2*x_3*x_4*x_5^2-1671*x_0*x_2*x_3*x_4*x_5^2+403*x_1*x_2*x_3*x_4*x_5^2-5852*x_2^2*x_3*x_4*x_5^2+14243*x_0*x_3^2*x_4*x_5^2+5933*x_1*x_3^2*x_4*x_5^2+9434*x_2*x_3^2*x_4*x_5^2-12529*x_3^3*x_4*x_5^2-7565*x_0^3*x_5^3-5518*x_0^2*x_1*x_5^3+15413*x_0*x_1^2*x_5^3-7786*x_0^2*x_2*x_5^3+12503*x_0*x_1*x_2*x_5^3-684*x_1^2*x_2*x_5^3-11603*x_0*x_2^2*x_5^3-10201*x_1*x_2^2*x_5^3-14676*x_2^3*x_5^3+7992*x_0^2*x_3*x_5^3-1174*x_0*x_1*x_3*x_5^3-219*x_1^2*x_3*x_5^3+2191*x_0*x_2*x_3*x_5^3-3548*x_1*x_2*x_3*x_5^3+262*x_2^2*x_3*x_5^3+5712*x_0*x_3^2*x_5^3-12934*x_1*x_3^2*x_5^3-8991*x_2*x_3^2*x_5^3+7445*x_3^3*x_5^3+12984*x_0^3*x_4^2*x_6-893*x_0^2*x_1*x_4^2*x_6-8208*x_0*x_1^2*x_4^2*x_6-9597*x_1^3*x_4^2*x_6+4335*x_0^2*x_2*x_4^2*x_6-12087*x_0*x_1*x_2*x_4^2*x_6-2264*x_1^2*x_2*x_4^2*x_6+3261*x_0*x_2^2*x_4^2*x_6+9538*x_1*x_2^2*x_4^2*x_6+6188*x_2^3*x_4^2*x_6-9994*x_0^2*x_3*x_4^2*x_6+8178*x_0*x_1*x_3*x_4^2*x_6-8061*x_1^2*x_3*x_4^2*x_6+14888*x_0*x_2*x_3*x_4^2*x_6-8932*x_1*x_2*x_3*x_4^2*x_6-7814*x_2^2*x_3*x_4^2*x_6-15660*x_0*x_3^2*x_4^2*x_6-8352*x_1*x_3^2*x_4^2*x_6-4794*x_2*x_3^2*x_4^2*x_6+13849*x_3^3*x_4^2*x_6-8626*x_0^3*x_4*x_5*x_6-1688*x_0^2*x_1*x_4*x_5*x_6+2319*x_0*x_1^2*x_4*x_5*x_6+492*x_1^3*x_4*x_5*x_6+14465*x_0^2*x_2*x_4*x_5*x_6-12166*x_0*x_1*x_2*x_4*x_5*x_6-3521*x_1^2*x_2*x_4*x_5*x_6-15360*x_0*x_2^2*x_4*x_5*x_6+4788*x_1*x_2^2*x_4*x_5*x_6+352*x_2^3*x_4*x_5*x_6-3049*x_0^2*x_3*x_4*x_5*x_6+4503*x_0*x_1*x_3*x_4*x_5*x_6+13373*x_1^2*x_3*x_4*x_5*x_6-6486*x_0*x_2*x_3*x_4*x_5*x_6+1342*x_1*x_2*x_3*x_4*x_5*x_6-13991*x_2^2*x_3*x_4*x_5*x_6-8608*x_0*x_3^2*x_4*x_5*x_6+4385*x_1*x_3^2*x_4*x_5*x_6+3027*x_2*x_3^2*x_4*x_5*x_6-12826*x_3^3*x_4*x_5*x_6+6514*x_0^3*x_5^2*x_6-4112*x_0^2*x_1*x_5^2*x_6-11876*x_0*x_1^2*x_5^2*x_6+684*x_1^3*x_5^2*x_6+10103*x_0^2*x_2*x_5^2*x_6-7689*x_0*x_1*x_2*x_5^2*x_6-6214*x_1^2*x_2*x_5^2*x_6+2786*x_0*x_2^2*x_5^2*x_6+5734*x_1*x_2^2*x_5^2*x_6+14952*x_2^3*x_5^2*x_6+1920*x_0^2*x_3*x_5^2*x_6+6090*x_0*x_1*x_3*x_5^2*x_6-7133*x_1^2*x_3*x_5^2*x_6+7082*x_0*x_2*x_3*x_5^2*x_6-11923*x_1*x_2*x_3*x_5^2*x_6+7930*x_2^2*x_3*x_5^2*x_6+8454*x_0*x_3^2*x_5^2*x_6-9385*x_1*x_3^2*x_5^2*x_6-10012*x_2*x_3^2*x_5^2*x_6+4332*x_3^3*x_5^2*x_6+11230*x_0^3*x_4*x_6^2-5234*x_0^2*x_1*x_4*x_6^2-12785*x_0*x_1^2*x_4*x_6^2-14653*x_1^3*x_4*x_6^2-2003*x_0^2*x_2*x_4*x_6^2+12802*x_0*x_1*x_2*x_4*x_6^2-3898*x_1^2*x_2*x_4*x_6^2+3475*x_0*x_2^2*x_4*x_6^2-584*x_1*x_2^2*x_4*x_6^2+2602*x_2^3*x_4*x_6^2-11175*x_0^2*x_3*x_4*x_6^2+4948*x_0*x_1*x_3*x_4*x_6^2+10773*x_1^2*x_3*x_4*x_6^2-1781*x_0*x_2*x_3*x_4*x_6^2-3828*x_1*x_2*x_3*x_4*x_6^2+580*x_2^2*x_3*x_4*x_6^2+9872*x_0*x_3^2*x_4*x_6^2+1744*x_1*x_3^2*x_4*x_6^2-5394*x_2*x_3^2*x_4*x_6^2+3966*x_3^3*x_4*x_6^2+15814*x_0^3*x_5*x_6^2-836*x_0^2*x_1*x_5*x_6^2-4913*x_0*x_1^2*x_5*x_6^2-6398*x_1^3*x_5*x_6^2-14572*x_0^2*x_2*x_5*x_6^2+9791*x_0*x_1*x_2*x_5*x_6^2+1976*x_1^2*x_2*x_5*x_6^2-11982*x_0*x_2^2*x_5*x_6^2-450*x_1*x_2^2*x_5*x_6^2+8935*x_2^3*x_5*x_6^2-12724*x_0^2*x_3*x_5*x_6^2-11356*x_0*x_1*x_3*x_5*x_6^2+6333*x_1^2*x_3*x_5*x_6^2-13025*x_0*x_2*x_3*x_5*x_6^2+3846*x_1*x_2*x_3*x_5*x_6^2+13932*x_2^2*x_3*x_5*x_6^2-699*x_0*x_3^2*x_5*x_6^2-2213*x_1*x_3^2*x_5*x_6^2-4872*x_2*x_3^2*x_5*x_6^2-8443*x_3^3*x_5*x_6^2+13217*x_0^3*x_6^3-2039*x_0^2*x_1*x_6^3-14816*x_0*x_1^2*x_6^3+5998*x_1^3*x_6^3-9663*x_0^2*x_2*x_6^3-15538*x_0*x_1*x_2*x_6^3-2673*x_1^2*x_2*x_6^3-2602*x_0*x_2^2*x_6^3-15180*x_1*x_2^2*x_6^3-12189*x_0^2*x_3*x_6^3+5683*x_0*x_1*x_3*x_6^3+2009*x_1^2*x_3*x_6^3+8464*x_0*x_2*x_3*x_6^3+13774*x_1*x_2*x_3*x_6^3+13576*x_2^2*x_3*x_6^3-13934*x_0*x_3^2*x_6^3-234*x_1*x_3^2*x_6^3-800*x_2*x_3^2*x_6^3-6927*x_3^3*x_6^3-7459*x_0^3*x_4^2*x_7-16142*x_0^2*x_1*x_4^2*x_7-3168*x_0*x_1^2*x_4^2*x_7+9296*x_1^3*x_4^2*x_7-1153*x_0^2*x_2*x_4^2*x_7-1798*x_0*x_1*x_2*x_4^2*x_7+5285*x_1^2*x_2*x_4^2*x_7-6834*x_0*x_2^2*x_4^2*x_7-13257*x_1*x_2^2*x_4^2*x_7-485*x_2^3*x_4^2*x_7+13363*x_0^2*x_3*x_4^2*x_7-5512*x_0*x_1*x_3*x_4^2*x_7+4748*x_1^2*x_3*x_4^2*x_7+2219*x_0*x_2*x_3*x_4^2*x_7-7388*x_1*x_2*x_3*x_4^2*x_7+1007*x_2^2*x_3*x_4^2*x_7+11091*x_0*x_3^2*x_4^2*x_7-493*x_1*x_3^2*x_4^2*x_7-3480*x_2*x_3^2*x_4^2*x_7+3105*x_3^3*x_4^2*x_7-6591*x_0^3*x_4*x_5*x_7+7251*x_0^2*x_1*x_4*x_5*x_7-7585*x_0*x_1^2*x_4*x_5*x_7+8293*x_1^3*x_4*x_5*x_7-2358*x_0^2*x_2*x_4*x_5*x_7-1576*x_0*x_1*x_2*x_4*x_5*x_7-9069*x_1^2*x_2*x_4*x_5*x_7+15511*x_0*x_2^2*x_4*x_5*x_7+3820*x_1*x_2^2*x_4*x_5*x_7+11118*x_2^3*x_4*x_5*x_7-9794*x_0^2*x_3*x_4*x_5*x_7+11614*x_0*x_1*x_3*x_4*x_5*x_7-12197*x_1^2*x_3*x_4*x_5*x_7-5138*x_0*x_2*x_3*x_4*x_5*x_7+1064*x_1*x_2*x_3*x_4*x_5*x_7+11566*x_2^2*x_3*x_4*x_5*x_7+11951*x_0*x_3^2*x_4*x_5*x_7-5501*x_1*x_3^2*x_4*x_5*x_7-6154*x_2*x_3^2*x_4*x_5*x_7-13107*x_3^3*x_4*x_5*x_7-12736*x_0^3*x_5^2*x_7-52*x_0^2*x_1*x_5^2*x_7-10450*x_0*x_1^2*x_5^2*x_7+8159*x_1^3*x_5^2*x_7-1019*x_0^2*x_2*x_5^2*x_7+15030*x_0*x_1*x_2*x_5^2*x_7+15191*x_1^2*x_2*x_5^2*x_7+13032*x_0*x_2^2*x_5^2*x_7+3039*x_1*x_2^2*x_5^2*x_7-6832*x_2^3*x_5^2*x_7-12534*x_0^2*x_3*x_5^2*x_7+247*x_0*x_1*x_3*x_5^2*x_7+4371*x_1^2*x_3*x_5^2*x_7+1168*x_0*x_2*x_3*x_5^2*x_7-8760*x_1*x_2*x_3*x_5^2*x_7-4540*x_2^2*x_3*x_5^2*x_7-6892*x_0*x_3^2*x_5^2*x_7-8261*x_1*x_3^2*x_5^2*x_7-6332*x_2*x_3^2*x_5^2*x_7-11119*x_3^3*x_5^2*x_7+13252*x_0^3*x_4*x_6*x_7-3872*x_0^2*x_1*x_4*x_6*x_7-11479*x_0*x_1^2*x_4*x_6*x_7+16100*x_1^3*x_4*x_6*x_7+4253*x_0^2*x_2*x_4*x_6*x_7+12634*x_0*x_1*x_2*x_4*x_6*x_7-16342*x_1^2*x_2*x_4*x_6*x_7-14281*x_0*x_2^2*x_4*x_6*x_7+4316*x_1*x_2^2*x_4*x_6*x_7-11209*x_2^3*x_4*x_6*x_7+1069*x_0^2*x_3*x_4*x_6*x_7-7918*x_0*x_1*x_3*x_4*x_6*x_7-12473*x_1^2*x_3*x_4*x_6*x_7-15312*x_0*x_2*x_3*x_4*x_6*x_7-11979*x_1*x_2*x_3*x_4*x_6*x_7-11611*x_2^2*x_3*x_4*x_6*x_7-16321*x_0*x_3^2*x_4*x_6*x_7+4544*x_1*x_3^2*x_4*x_6*x_7+4747*x_2*x_3^2*x_4*x_6*x_7+9962*x_3^3*x_4*x_6*x_7-5635*x_0^3*x_5*x_6*x_7-13116*x_0^2*x_1*x_5*x_6*x_7+3801*x_0*x_1^2*x_5*x_6*x_7-6715*x_1^3*x_5*x_6*x_7-12096*x_0^2*x_2*x_5*x_6*x_7-6252*x_0*x_1*x_2*x_5*x_6*x_7+16299*x_1^2*x_2*x_5*x_6*x_7-9847*x_0*x_2^2*x_5*x_6*x_7-11372*x_1*x_2^2*x_5*x_6*x_7-343*x_2^3*x_5*x_6*x_7-10651*x_0^2*x_3*x_5*x_6*x_7-8805*x_0*x_1*x_3*x_5*x_6*x_7-15947*x_1^2*x_3*x_5*x_6*x_7+4204*x_0*x_2*x_3*x_5*x_6*x_7+13372*x_1*x_2*x_3*x_5*x_6*x_7-7041*x_2^2*x_3*x_5*x_6*x_7+6126*x_0*x_3^2*x_5*x_6*x_7-2154*x_1*x_3^2*x_5*x_6*x_7-2664*x_2*x_3^2*x_5*x_6*x_7-13769*x_3^3*x_5*x_6*x_7+2238*x_0^3*x_6^2*x_7+12617*x_0^2*x_1*x_6^2*x_7-3892*x_0*x_1^2*x_6^2*x_7+10060*x_1^3*x_6^2*x_7-1763*x_0^2*x_2*x_6^2*x_7+4887*x_0*x_1*x_2*x_6^2*x_7-741*x_1^2*x_2*x_6^2*x_7+11685*x_0*x_2^2*x_6^2*x_7-493*x_1*x_2^2*x_6^2*x_7-13576*x_2^3*x_6^2*x_7-15476*x_0^2*x_3*x_6^2*x_7+14930*x_0*x_1*x_3*x_6^2*x_7+3223*x_1^2*x_3*x_6^2*x_7+1167*x_0*x_2*x_3*x_6^2*x_7+3341*x_1*x_2*x_3*x_6^2*x_7-1481*x_2^2*x_3*x_6^2*x_7-2494*x_0*x_3^2*x_6^2*x_7+2088*x_1*x_3^2*x_6^2*x_7-15844*x_2*x_3^2*x_6^2*x_7+10184*x_3^3*x_6^2*x_7+4679*x_0^3*x_4*x_7^2+11869*x_0^2*x_1*x_4*x_7^2-8284*x_0*x_1^2*x_4*x_7^2+8102*x_1^3*x_4*x_7^2-7238*x_0^2*x_2*x_4*x_7^2+1059*x_0*x_1*x_2*x_4*x_7^2-15793*x_1^2*x_2*x_4*x_7^2+2359*x_0*x_2^2*x_4*x_7^2+9126*x_1*x_2^2*x_4*x_7^2+2677*x_2^3*x_4*x_7^2-11773*x_0^2*x_3*x_4*x_7^2-12799*x_0*x_1*x_3*x_4*x_7^2-6580*x_1^2*x_3*x_4*x_7^2-11990*x_0*x_2*x_3*x_4*x_7^2+5196*x_1*x_2*x_3*x_4*x_7^2-5459*x_2^2*x_3*x_4*x_7^2-12949*x_0*x_3^2*x_4*x_7^2-1263*x_1*x_3^2*x_4*x_7^2+9876*x_2*x_3^2*x_4*x_7^2+11286*x_3^3*x_4*x_7^2-5357*x_0^3*x_5*x_7^2-10985*x_0^2*x_1*x_5*x_7^2-13753*x_0*x_1^2*x_5*x_7^2-5562*x_1^3*x_5*x_7^2+9816*x_0^2*x_2*x_5*x_7^2+10510*x_0*x_1*x_2*x_5*x_7^2+5758*x_1^2*x_2*x_5*x_7^2-1563*x_0*x_2^2*x_5*x_7^2-33*x_1*x_2^2*x_5*x_7^2+11636*x_2^3*x_5*x_7^2+5152*x_0^2*x_3*x_5*x_7^2+10376*x_0*x_1*x_3*x_5*x_7^2+5308*x_1^2*x_3*x_5*x_7^2+6723*x_0*x_2*x_3*x_5*x_7^2-8585*x_1*x_2*x_3*x_5*x_7^2-5114*x_2^2*x_3*x_5*x_7^2-3597*x_0*x_3^2*x_5*x_7^2-440*x_1*x_3^2*x_5*x_7^2-5864*x_2*x_3^2*x_5*x_7^2-12569*x_3^3*x_5*x_7^2-8404*x_0^3*x_6*x_7^2+611*x_0^2*x_1*x_6*x_7^2-2587*x_0*x_1^2*x_6*x_7^2-8754*x_1^3*x_6*x_7^2+4455*x_0^2*x_2*x_6*x_7^2+4055*x_0*x_1*x_2*x_6*x_7^2+5182*x_1^2*x_2*x_6*x_7^2+2920*x_0*x_2^2*x_6*x_7^2+15569*x_1*x_2^2*x_6*x_7^2+2281*x_2^3*x_6*x_7^2-8890*x_0^2*x_3*x_6*x_7^2+15940*x_0*x_1*x_3*x_6*x_7^2+7114*x_1^2*x_3*x_6*x_7^2+11225*x_0*x_2*x_3*x_6*x_7^2+9111*x_1*x_2*x_3*x_6*x_7^2+4680*x_2^2*x_3*x_6*x_7^2+6443*x_0*x_3^2*x_6*x_7^2-8176*x_1*x_3^2*x_6*x_7^2+8258*x_2*x_3^2*x_6*x_7^2-13773*x_3^3*x_6*x_7^2-2501*x_0^3*x_7^3+10798*x_0^2*x_1*x_7^3+7256*x_0*x_1^2*x_7^3+699*x_1^3*x_7^3-11232*x_0^2*x_2*x_7^3+4525*x_0*x_1*x_2*x_7^3+10356*x_1^2*x_2*x_7^3+8315*x_0*x_2^2*x_7^3+9004*x_1*x_2^2*x_7^3-14658*x_2^3*x_7^3+9844*x_0^2*x_3*x_7^3-10093*x_0*x_1*x_3*x_7^3-6178*x_1^2*x_3*x_7^3+5191*x_0*x_2*x_3*x_7^3+14585*x_1*x_2*x_3*x_7^3+14307*x_2^2*x_3*x_7^3-11286*x_0*x_3^2*x_7^3+13916*x_1*x_3^2*x_7^3+13773*x_2*x_3^2*x_7^3,-15542*x_0^3*x_4^3+4255*x_0^2*x_1*x_4^3-13421*x_0*x_1^2*x_4^3+8070*x_1^3*x_4^3+10428*x_0^2*x_2*x_4^3-11279*x_0*x_1*x_2*x_4^3+1175*x_1^2*x_2*x_4^3-5813*x_0*x_2^2*x_4^3-316*x_1*x_2^2*x_4^3-7297*x_2^3*x_4^3+4428*x_0^2*x_3*x_4^3+7557*x_0*x_1*x_3*x_4^3+11358*x_1^2*x_3*x_4^3-4019*x_0*x_2*x_3*x_4^3-12347*x_1*x_2*x_3*x_4^3+4464*x_2^2*x_3*x_4^3-13119*x_0*x_3^2*x_4^3-7593*x_1*x_3^2*x_4^3-2630*x_2*x_3^2*x_4^3+6870*x_3^3*x_4^3-9068*x_0^3*x_4^2*x_5+6194*x_0^2*x_1*x_4^2*x_5-479*x_0*x_1^2*x_4^2*x_5-12972*x_1^3*x_4^2*x_5+16064*x_0^2*x_2*x_4^2*x_5-12796*x_0*x_1*x_2*x_4^2*x_5-12140*x_1^2*x_2*x_4^2*x_5+852*x_0*x_2^2*x_4^2*x_5-4378*x_1*x_2^2*x_4^2*x_5+3569*x_2^3*x_4^2*x_5+16050*x_0^2*x_3*x_4^2*x_5+10730*x_0*x_1*x_3*x_4^2*x_5-5894*x_1^2*x_3*x_4^2*x_5+14700*x_0*x_2*x_3*x_4^2*x_5-1979*x_1*x_2*x_3*x_4^2*x_5+10706*x_2^2*x_3*x_4^2*x_5+7159*x_0*x_3^2*x_4^2*x_5-1606*x_1*x_3^2*x_4^2*x_5-5018*x_2*x_3^2*x_4^2*x_5-13377*x_3^3*x_4^2*x_5+12019*x_0^3*x_4*x_5^2+13644*x_0^2*x_1*x_4*x_5^2-15044*x_0*x_1^2*x_4*x_5^2+6243*x_1^3*x_4*x_5^2+4165*x_0^2*x_2*x_4*x_5^2-11828*x_0*x_1*x_2*x_4*x_5^2+9470*x_1^2*x_2*x_4*x_5^2-11551*x_0*x_2^2*x_4*x_5^2+16338*x_1*x_2^2*x_4*x_5^2+4245*x_2^3*x_4*x_5^2+7390*x_0^2*x_3*x_4*x_5^2-9687*x_0*x_1*x_3*x_4*x_5^2+14105*x_1^2*x_3*x_4*x_5^2+16069*x_0*x_2*x_3*x_4*x_5^2+14253*x_1*x_2*x_3*x_4*x_5^2-4231*x_2^2*x_3*x_4*x_5^2-12221*x_0*x_3^2*x_4*x_5^2+10343*x_1*x_3^2*x_4*x_5^2-3247*x_2*x_3^2*x_4*x_5^2+7730*x_3^3*x_4*x_5^2-8689*x_0^3*x_5^3+7689*x_0^2*x_1*x_5^3-7305*x_0*x_1^2*x_5^3+2660*x_0^2*x_2*x_5^3-15098*x_0*x_1*x_2*x_5^3+5728*x_1^2*x_2*x_5^3+14433*x_0*x_2^2*x_5^3+10687*x_1*x_2^2*x_5^3+12622*x_2^3*x_5^3-5161*x_0^2*x_3*x_5^3+9115*x_0*x_1*x_3*x_5^3+11771*x_1^2*x_3*x_5^3-5372*x_0*x_2*x_3*x_5^3+14545*x_1*x_2*x_3*x_5^3+12533*x_2^2*x_3*x_5^3+7612*x_0*x_3^2*x_5^3-3848*x_1*x_3^2*x_5^3+5770*x_2*x_3^2*x_5^3-7408*x_3^3*x_5^3+12545*x_0^3*x_4^2*x_6-3775*x_0^2*x_1*x_4^2*x_6+14786*x_0*x_1^2*x_4^2*x_6+9838*x_1^3*x_4^2*x_6-1852*x_0^2*x_2*x_4^2*x_6+5390*x_0*x_1*x_2*x_4^2*x_6+8001*x_1^2*x_2*x_4^2*x_6+12484*x_0*x_2^2*x_4^2*x_6-13222*x_1*x_2^2*x_4^2*x_6+10043*x_2^3*x_4^2*x_6-7203*x_0^2*x_3*x_4^2*x_6-11461*x_0*x_1*x_3*x_4^2*x_6-1265*x_1^2*x_3*x_4^2*x_6-712*x_0*x_2*x_3*x_4^2*x_6-1394*x_1*x_2*x_3*x_4^2*x_6+5723*x_2^2*x_3*x_4^2*x_6+13439*x_0*x_3^2*x_4^2*x_6-15164*x_1*x_3^2*x_4^2*x_6+16230*x_2*x_3^2*x_4^2*x_6-5765*x_3^3*x_4^2*x_6-13613*x_0^3*x_4*x_5*x_6+4971*x_0^2*x_1*x_4*x_5*x_6-8154*x_0*x_1^2*x_4*x_5*x_6+14690*x_1^3*x_4*x_5*x_6+2406*x_0^2*x_2*x_4*x_5*x_6-2334*x_0*x_1*x_2*x_4*x_5*x_6-6287*x_1^2*x_2*x_4*x_5*x_6-11618*x_0*x_2^2*x_4*x_5*x_6-8639*x_1*x_2^2*x_4*x_5*x_6+7059*x_2^3*x_4*x_5*x_6+8480*x_0^2*x_3*x_4*x_5*x_6-13236*x_0*x_1*x_3*x_4*x_5*x_6-7232*x_1^2*x_3*x_4*x_5*x_6+8115*x_0*x_2*x_3*x_4*x_5*x_6-363*x_1*x_2*x_3*x_4*x_5*x_6+803*x_2^2*x_3*x_4*x_5*x_6+3416*x_0*x_3^2*x_4*x_5*x_6+15003*x_1*x_3^2*x_4*x_5*x_6-13345*x_2*x_3^2*x_4*x_5*x_6+9286*x_3^3*x_4*x_5*x_6+16068*x_0^3*x_5^2*x_6-6431*x_0^2*x_1*x_5^2*x_6+3245*x_0*x_1^2*x_5^2*x_6-5728*x_1^3*x_5^2*x_6-9872*x_0^2*x_2*x_5^2*x_6+7070*x_0*x_1*x_2*x_5^2*x_6+1878*x_1^2*x_2*x_5^2*x_6+2157*x_0*x_2^2*x_5^2*x_6+8294*x_1*x_2^2*x_5^2*x_6+10469*x_2^3*x_5^2*x_6-2905*x_0^2*x_3*x_5^2*x_6-13644*x_0*x_1*x_3*x_5^2*x_6+11858*x_1^2*x_3*x_5^2*x_6+10284*x_0*x_2*x_3*x_5^2*x_6-12812*x_1*x_2*x_3*x_5^2*x_6+16056*x_2^2*x_3*x_5^2*x_6-1490*x_0*x_3^2*x_5^2*x_6+14756*x_1*x_3^2*x_5^2*x_6-16012*x_2*x_3^2*x_5^2*x_6+8307*x_3^3*x_5^2*x_6+5159*x_0^3*x_4*x_6^2+1368*x_0^2*x_1*x_4*x_6^2-3215*x_0*x_1^2*x_4*x_6^2-6081*x_1^3*x_4*x_6^2+10807*x_0^2*x_2*x_4*x_6^2+13169*x_0*x_1*x_2*x_4*x_6^2+10564*x_1^2*x_2*x_4*x_6^2+13159*x_0*x_2^2*x_4*x_6^2+14795*x_1*x_2^2*x_4*x_6^2-1928*x_2^3*x_4*x_6^2-953*x_0^2*x_3*x_4*x_6^2-15457*x_0*x_1*x_3*x_4*x_6^2-13487*x_1^2*x_3*x_4*x_6^2-5955*x_0*x_2*x_3*x_4*x_6^2-12044*x_1*x_2*x_3*x_4*x_6^2+3943*x_2^2*x_3*x_4*x_6^2-5575*x_0*x_3^2*x_4*x_6^2+1289*x_1*x_3^2*x_4*x_6^2+2742*x_2*x_3^2*x_4*x_6^2-3161*x_3^3*x_4*x_6^2+9539*x_0^3*x_5*x_6^2+11693*x_0^2*x_1*x_5*x_6^2-7674*x_0*x_1^2*x_5*x_6^2+11487*x_1^3*x_5*x_6^2-13798*x_0^2*x_2*x_5*x_6^2+5213*x_0*x_1*x_2*x_5*x_6^2-8188*x_1^2*x_2*x_5*x_6^2+8427*x_0*x_2^2*x_5*x_6^2+9281*x_1*x_2^2*x_5*x_6^2-2994*x_2^3*x_5*x_6^2-6213*x_0^2*x_3*x_5*x_6^2-4494*x_0*x_1*x_3*x_5*x_6^2-13036*x_1^2*x_3*x_5*x_6^2-11539*x_0*x_2*x_3*x_5*x_6^2-1056*x_1*x_2*x_3*x_5*x_6^2-393*x_2^2*x_3*x_5*x_6^2+12090*x_0*x_3^2*x_5*x_6^2+15572*x_1*x_3^2*x_5*x_6^2+16309*x_2*x_3^2*x_5*x_6^2-3566*x_3^3*x_5*x_6^2-7096*x_0^3*x_6^3+15119*x_0^2*x_1*x_6^3-4523*x_0*x_1^2*x_6^3+15042*x_1^3*x_6^3+9547*x_0^2*x_2*x_6^3+8609*x_0*x_1*x_2*x_6^3-2212*x_1^2*x_2*x_6^3+1928*x_0*x_2^2*x_6^3+2550*x_1*x_2^2*x_6^3+11842*x_0^2*x_3*x_6^3-6805*x_0*x_1*x_3*x_6^3+13297*x_1^2*x_3*x_6^3-5672*x_0*x_2*x_3*x_6^3-11062*x_1*x_2*x_3*x_6^3-3707*x_2^2*x_3*x_6^3+1682*x_0*x_3^2*x_6^3-10133*x_1*x_3^2*x_6^3-12274*x_2*x_3^2*x_6^3-4318*x_3^3*x_6^3-3645*x_0^3*x_4^2*x_7+1879*x_0^2*x_1*x_4^2*x_7-15822*x_0*x_1^2*x_4^2*x_7-393*x_1^3*x_4^2*x_7+10787*x_0^2*x_2*x_4^2*x_7-4952*x_0*x_1*x_2*x_4^2*x_7-12450*x_1^2*x_2*x_4^2*x_7-14618*x_0*x_2^2*x_4^2*x_7+9270*x_1*x_2^2*x_4^2*x_7+867*x_2^3*x_4^2*x_7+15715*x_0^2*x_3*x_4^2*x_7+7100*x_0*x_1*x_3*x_4^2*x_7-16239*x_1^2*x_3*x_4^2*x_7-10351*x_0*x_2*x_3*x_4^2*x_7+1280*x_1*x_2*x_3*x_4^2*x_7-12762*x_2^2*x_3*x_4^2*x_7+16204*x_0*x_3^2*x_4^2*x_7-3627*x_1*x_3^2*x_4^2*x_7+10519*x_2*x_3^2*x_4^2*x_7-5553*x_3^3*x_4^2*x_7+1224*x_0^3*x_4*x_5*x_7+12200*x_0^2*x_1*x_4*x_5*x_7-9180*x_0*x_1^2*x_4*x_5*x_7+10599*x_1^3*x_4*x_5*x_7+9958*x_0^2*x_2*x_4*x_5*x_7-470*x_0*x_1*x_2*x_4*x_5*x_7+1049*x_1^2*x_2*x_4*x_5*x_7-15262*x_0*x_2^2*x_4*x_5*x_7-14987*x_1*x_2^2*x_4*x_5*x_7+3795*x_2^3*x_4*x_5*x_7-1677*x_0^2*x_3*x_4*x_5*x_7-9542*x_0*x_1*x_3*x_4*x_5*x_7-6368*x_1^2*x_3*x_4*x_5*x_7+8574*x_0*x_2*x_3*x_4*x_5*x_7+5376*x_1*x_2*x_3*x_4*x_5*x_7+3238*x_2^2*x_3*x_4*x_5*x_7+8342*x_0*x_3^2*x_4*x_5*x_7+10323*x_1*x_3^2*x_4*x_5*x_7+7209*x_2*x_3^2*x_4*x_5*x_7-11513*x_3^3*x_4*x_5*x_7+14115*x_0^3*x_5^2*x_7+6155*x_0^2*x_1*x_5^2*x_7+1618*x_0*x_1^2*x_5^2*x_7-8297*x_1^3*x_5^2*x_7+1842*x_0^2*x_2*x_5^2*x_7+9384*x_0*x_1*x_2*x_5^2*x_7-15409*x_1^2*x_2*x_5^2*x_7-14909*x_0*x_2^2*x_5^2*x_7+13574*x_1*x_2^2*x_5^2*x_7-1333*x_2^3*x_5^2*x_7-14304*x_0^2*x_3*x_5^2*x_7-3869*x_0*x_1*x_3*x_5^2*x_7+2990*x_1^2*x_3*x_5^2*x_7-13738*x_0*x_2*x_3*x_5^2*x_7+15595*x_1*x_2*x_3*x_5^2*x_7+2526*x_2^2*x_3*x_5^2*x_7+12784*x_0*x_3^2*x_5^2*x_7-9039*x_1*x_3^2*x_5^2*x_7+3439*x_2*x_3^2*x_5^2*x_7+6669*x_3^3*x_5^2*x_7-13395*x_0^3*x_4*x_6*x_7+3344*x_0^2*x_1*x_4*x_6*x_7-13573*x_0*x_1^2*x_4*x_6*x_7-8954*x_1^3*x_4*x_6*x_7-5500*x_0^2*x_2*x_4*x_6*x_7-3009*x_0*x_1*x_2*x_4*x_6*x_7-617*x_1^2*x_2*x_4*x_6*x_7+5178*x_0*x_2^2*x_4*x_6*x_7-11338*x_1*x_2^2*x_4*x_6*x_7+4817*x_2^3*x_4*x_6*x_7-10771*x_0^2*x_3*x_4*x_6*x_7-10997*x_0*x_1*x_3*x_4*x_6*x_7-11653*x_1^2*x_3*x_4*x_6*x_7-891*x_0*x_2*x_3*x_4*x_6*x_7+9470*x_1*x_2*x_3*x_4*x_6*x_7+6716*x_2^2*x_3*x_4*x_6*x_7+12817*x_0*x_3^2*x_4*x_6*x_7-12375*x_1*x_3^2*x_4*x_6*x_7-4868*x_2*x_3^2*x_4*x_6*x_7-9536*x_3^3*x_4*x_6*x_7+7669*x_0^3*x_5*x_6*x_7+10084*x_0^2*x_1*x_5*x_6*x_7+11491*x_0*x_1^2*x_5*x_6*x_7-13760*x_1^3*x_5*x_6*x_7+395*x_0^2*x_2*x_5*x_6*x_7+8958*x_0*x_1*x_2*x_5*x_6*x_7-11694*x_1^2*x_2*x_5*x_6*x_7+11113*x_0*x_2^2*x_5*x_6*x_7-13050*x_1*x_2^2*x_5*x_6*x_7-4492*x_2^3*x_5*x_6*x_7-14488*x_0^2*x_3*x_5*x_6*x_7+12542*x_0*x_1*x_3*x_5*x_6*x_7+4092*x_1^2*x_3*x_5*x_6*x_7+3880*x_0*x_2*x_3*x_5*x_6*x_7-11377*x_1*x_2*x_3*x_5*x_6*x_7-3087*x_2^2*x_3*x_5*x_6*x_7+8611*x_0*x_3^2*x_5*x_6*x_7+4866*x_1*x_3^2*x_5*x_6*x_7+8867*x_2*x_3^2*x_5*x_6*x_7+6712*x_3^3*x_5*x_6*x_7-11435*x_0^3*x_6^2*x_7+1677*x_0^2*x_1*x_6^2*x_7+7014*x_0*x_1^2*x_6^2*x_7+14505*x_1^3*x_6^2*x_7-2867*x_0^2*x_2*x_6^2*x_7+15213*x_0*x_1*x_2*x_6^2*x_7-6479*x_1^2*x_2*x_6^2*x_7-12874*x_0*x_2^2*x_6^2*x_7+6266*x_1*x_2^2*x_6^2*x_7+3707*x_2^3*x_6^2*x_7-7473*x_0^2*x_3*x_6^2*x_7-14651*x_0*x_1*x_3*x_6^2*x_7+10523*x_1^2*x_3*x_6^2*x_7-13174*x_0*x_2*x_3*x_6^2*x_7-5945*x_1*x_2*x_3*x_6^2*x_7+5247*x_2^2*x_3*x_6^2*x_7+8164*x_0*x_3^2*x_6^2*x_7+14087*x_1*x_3^2*x_6^2*x_7+5084*x_2*x_3^2*x_6^2*x_7+11599*x_3^3*x_6^2*x_7+2404*x_0^3*x_4*x_7^2-11819*x_0^2*x_1*x_4*x_7^2-13725*x_0*x_1^2*x_4*x_7^2-11610*x_1^3*x_4*x_7^2-9791*x_0^2*x_2*x_4*x_7^2+3437*x_0*x_1*x_2*x_4*x_7^2+1803*x_1^2*x_2*x_4*x_7^2+914*x_0*x_2^2*x_4*x_7^2-8748*x_1*x_2^2*x_4*x_7^2-2476*x_2^3*x_4*x_7^2-12128*x_0^2*x_3*x_4*x_7^2-2148*x_0*x_1*x_3*x_4*x_7^2-315*x_1^2*x_3*x_4*x_7^2+11395*x_0*x_2*x_3*x_4*x_7^2-11709*x_1*x_2*x_3*x_4*x_7^2+16267*x_2^2*x_3*x_4*x_7^2+14657*x_0*x_3^2*x_4*x_7^2-11091*x_1*x_3^2*x_4*x_7^2+9142*x_2*x_3^2*x_4*x_7^2+13174*x_3^3*x_4*x_7^2-6201*x_0^3*x_5*x_7^2-5582*x_0^2*x_1*x_5*x_7^2-10763*x_0*x_1^2*x_5*x_7^2-13887*x_1^3*x_5*x_7^2+13238*x_0^2*x_2*x_5*x_7^2-172*x_0*x_1*x_2*x_5*x_7^2+9728*x_1^2*x_2*x_5*x_7^2+12837*x_0*x_2^2*x_5*x_7^2-11641*x_1*x_2^2*x_5*x_7^2+15333*x_2^3*x_5*x_7^2+248*x_0^2*x_3*x_5*x_7^2+6168*x_0*x_1*x_3*x_5*x_7^2+3074*x_1^2*x_3*x_5*x_7^2-1372*x_0*x_2*x_3*x_5*x_7^2-4905*x_1*x_2*x_3*x_5*x_7^2+1126*x_2^2*x_3*x_5*x_7^2-14795*x_0*x_3^2*x_5*x_7^2-12869*x_1*x_3^2*x_5*x_7^2+1485*x_2*x_3^2*x_5*x_7^2+13472*x_3^3*x_5*x_7^2-5939*x_0^3*x_6*x_7^2+12298*x_0^2*x_1*x_6*x_7^2-1232*x_0*x_1^2*x_6*x_7^2-651*x_1^3*x_6*x_7^2-11586*x_0^2*x_2*x_6*x_7^2-15207*x_0*x_1*x_2*x_6*x_7^2+10310*x_1^2*x_2*x_6*x_7^2+16010*x_0*x_2^2*x_6*x_7^2-8578*x_1*x_2^2*x_6*x_7^2+7027*x_2^3*x_6*x_7^2+2061*x_0^2*x_3*x_6*x_7^2-6336*x_0*x_1*x_3*x_6*x_7^2+14459*x_1^2*x_3*x_6*x_7^2+10070*x_0*x_2*x_3*x_6*x_7^2-8146*x_1*x_2*x_3*x_6*x_7^2-1849*x_2^2*x_3*x_6*x_7^2+11811*x_0*x_3^2*x_6*x_7^2-8436*x_1*x_3^2*x_6*x_7^2+15755*x_2*x_3^2*x_6*x_7^2+5853*x_3^3*x_6*x_7^2-14921*x_0^3*x_7^3+9912*x_0^2*x_1*x_7^3+13278*x_0*x_1^2*x_7^3-3410*x_1^3*x_7^3+7210*x_0^2*x_2*x_7^3+10794*x_0*x_1*x_2*x_7^3+3425*x_1^2*x_2*x_7^3-5126*x_0*x_2^2*x_7^3+5463*x_1*x_2^2*x_7^3+1083*x_2^3*x_7^3-9104*x_0^2*x_3*x_7^3-12367*x_0*x_1*x_3*x_7^3-12631*x_1^2*x_3*x_7^3-7052*x_0*x_2*x_3*x_7^3+14477*x_1*x_2*x_3*x_7^3+5395*x_2^2*x_3*x_7^3-13174*x_0*x_3^2*x_7^3-12887*x_1*x_3^2*x_7^3-5853*x_2*x_3^2*x_7^3,-6554*x_0^3*x_4^3+7424*x_0^2*x_1*x_4^3-4297*x_0*x_1^2*x_4^3-8561*x_1^3*x_4^3+2347*x_0^2*x_2*x_4^3+12428*x_0*x_1*x_2*x_4^3+5113*x_1^2*x_2*x_4^3+6897*x_0*x_2^2*x_4^3-2356*x_1*x_2^2*x_4^3+12162*x_2^3*x_4^3+4612*x_0^2*x_3*x_4^3-11588*x_0*x_1*x_3*x_4^3+10846*x_1^2*x_3*x_4^3-943*x_0*x_2*x_3*x_4^3+15736*x_1*x_2*x_3*x_4^3+5113*x_2^2*x_3*x_4^3+9027*x_0*x_3^2*x_4^3+8977*x_1*x_3^2*x_4^3+477*x_2*x_3^2*x_4^3-4043*x_3^3*x_4^3+10257*x_0^3*x_4^2*x_5+1283*x_0^2*x_1*x_4^2*x_5+6483*x_0*x_1^2*x_4^2*x_5+14573*x_1^3*x_4^2*x_5-10865*x_0^2*x_2*x_4^2*x_5-11797*x_0*x_1*x_2*x_4^2*x_5+14673*x_1^2*x_2*x_4^2*x_5-5787*x_0*x_2^2*x_4^2*x_5-3509*x_1*x_2^2*x_4^2*x_5+6117*x_2^3*x_4^2*x_5+13771*x_0^2*x_3*x_4^2*x_5-66*x_0*x_1*x_3*x_4^2*x_5-13277*x_1^2*x_3*x_4^2*x_5+15466*x_0*x_2*x_3*x_4^2*x_5+13953*x_1*x_2*x_3*x_4^2*x_5+5811*x_2^2*x_3*x_4^2*x_5-1975*x_0*x_3^2*x_4^2*x_5+3300*x_1*x_3^2*x_4^2*x_5-7372*x_2*x_3^2*x_4^2*x_5+6105*x_3^3*x_4^2*x_5-12362*x_0^3*x_4*x_5^2-11985*x_0^2*x_1*x_4*x_5^2-6344*x_0*x_1^2*x_4*x_5^2-1697*x_1^3*x_4*x_5^2+14849*x_0^2*x_2*x_4*x_5^2+15424*x_0*x_1*x_2*x_4*x_5^2+7092*x_1^2*x_2*x_4*x_5^2+10603*x_0*x_2^2*x_4*x_5^2+15566*x_1*x_2^2*x_4*x_5^2-4021*x_2^3*x_4*x_5^2+90*x_0^2*x_3*x_4*x_5^2+4587*x_0*x_1*x_3*x_4*x_5^2+2870*x_1^2*x_3*x_4*x_5^2+317*x_0*x_2*x_3*x_4*x_5^2+2373*x_1*x_2*x_3*x_4*x_5^2-7610*x_2^2*x_3*x_4*x_5^2+8654*x_0*x_3^2*x_4*x_5^2+13356*x_1*x_3^2*x_4*x_5^2+11539*x_2*x_3^2*x_4*x_5^2+10815*x_3^3*x_4*x_5^2-6246*x_0^3*x_5^3+3164*x_0^2*x_1*x_5^3-12499*x_0*x_1^2*x_5^3+5885*x_0^2*x_2*x_5^3-1022*x_0*x_1*x_2*x_5^3-15361*x_1^2*x_2*x_5^3+7440*x_0*x_2^2*x_5^3+12284*x_1*x_2^2*x_5^3-5564*x_2^3*x_5^3+5924*x_0^2*x_3*x_5^3+7440*x_0*x_1*x_3*x_5^3+10686*x_1^2*x_3*x_5^3+15042*x_0*x_2*x_3*x_5^3+950*x_1*x_2*x_3*x_5^3-5947*x_2^2*x_3*x_5^3-981*x_0*x_3^2*x_5^3+4108*x_1*x_3^2*x_5^3-9763*x_2*x_3^2*x_5^3-8557*x_3^3*x_5^3+8782*x_0^3*x_4^2*x_6-413*x_0^2*x_1*x_4^2*x_6-1615*x_0*x_1^2*x_4^2*x_6+14232*x_1^3*x_4^2*x_6+579*x_0^2*x_2*x_4^2*x_6+14210*x_0*x_1*x_2*x_4^2*x_6+14514*x_1^2*x_2*x_4^2*x_6+15991*x_0*x_2^2*x_4^2*x_6-12998*x_1*x_2^2*x_4^2*x_6+107*x_2^3*x_4^2*x_6+3982*x_0^2*x_3*x_4^2*x_6-5371*x_0*x_1*x_3*x_4^2*x_6-12113*x_1^2*x_3*x_4^2*x_6-2097*x_0*x_2*x_3*x_4^2*x_6+1271*x_1*x_2*x_3*x_4^2*x_6-9900*x_2^2*x_3*x_4^2*x_6+11362*x_0*x_3^2*x_4^2*x_6+11581*x_1*x_3^2*x_4^2*x_6+3514*x_2*x_3^2*x_4^2*x_6-5455*x_3^3*x_4^2*x_6-4234*x_0^3*x_4*x_5*x_6-10164*x_0^2*x_1*x_4*x_5*x_6-1944*x_0*x_1^2*x_4*x_5*x_6-12982*x_1^3*x_4*x_5*x_6-11052*x_0^2*x_2*x_4*x_5*x_6-1318*x_0*x_1*x_2*x_4*x_5*x_6+11781*x_1^2*x_2*x_4*x_5*x_6-15505*x_0*x_2^2*x_4*x_5*x_6-12369*x_1*x_2^2*x_4*x_5*x_6-5179*x_2^3*x_4*x_5*x_6+3931*x_0^2*x_3*x_4*x_5*x_6+15152*x_0*x_1*x_3*x_4*x_5*x_6+14145*x_1^2*x_3*x_4*x_5*x_6+11587*x_0*x_2*x_3*x_4*x_5*x_6-13908*x_1*x_2*x_3*x_4*x_5*x_6-7409*x_2^2*x_3*x_4*x_5*x_6+250*x_0*x_3^2*x_4*x_5*x_6+12878*x_1*x_3^2*x_4*x_5*x_6+2472*x_2*x_3^2*x_4*x_5*x_6+13291*x_3^3*x_4*x_5*x_6+7401*x_0^3*x_5^2*x_6+8992*x_0^2*x_1*x_5^2*x_6-4288*x_0*x_1^2*x_5^2*x_6+15361*x_1^3*x_5^2*x_6+15080*x_0^2*x_2*x_5^2*x_6+13623*x_0*x_1*x_2*x_5^2*x_6-10959*x_1^2*x_2*x_5^2*x_6+539*x_0*x_2^2*x_5^2*x_6+9970*x_1*x_2^2*x_5^2*x_6-14316*x_2^3*x_5^2*x_6+6347*x_0^2*x_3*x_5^2*x_6+13656*x_0*x_1*x_3*x_5^2*x_6+15262*x_1^2*x_3*x_5^2*x_6-5418*x_0*x_2*x_3*x_5^2*x_6+612*x_1*x_2*x_3*x_5^2*x_6+14957*x_2^2*x_3*x_5^2*x_6+3428*x_0*x_3^2*x_5^2*x_6+9353*x_1*x_3^2*x_5^2*x_6-2701*x_2*x_3^2*x_5^2*x_6-14593*x_3^3*x_5^2*x_6-5592*x_0^3*x_4*x_6^2-10459*x_0^2*x_1*x_4*x_6^2+12781*x_0*x_1^2*x_4*x_6^2-8893*x_1^3*x_4*x_6^2+3783*x_0^2*x_2*x_4*x_6^2-14962*x_0*x_1*x_2*x_4*x_6^2+867*x_1^2*x_2*x_4*x_6^2+340*x_0*x_2^2*x_4*x_6^2+5364*x_1*x_2^2*x_4*x_6^2+9440*x_2^3*x_4*x_6^2-11733*x_0^2*x_3*x_4*x_6^2-13711*x_0*x_1*x_3*x_4*x_6^2-10824*x_1^2*x_3*x_4*x_6^2+9082*x_0*x_2*x_3*x_4*x_6^2+901*x_1*x_2*x_3*x_4*x_6^2+7439*x_2^2*x_3*x_4*x_6^2+8358*x_0*x_3^2*x_4*x_6^2+4040*x_1*x_3^2*x_4*x_6^2-8412*x_2*x_3^2*x_4*x_6^2+2820*x_3^3*x_4*x_6^2-10414*x_0^3*x_5*x_6^2-15224*x_0^2*x_1*x_5*x_6^2-10780*x_0*x_1^2*x_5*x_6^2+14192*x_1^3*x_5*x_6^2+6239*x_0^2*x_2*x_5*x_6^2-15179*x_0*x_1*x_2*x_5*x_6^2-14482*x_1^2*x_2*x_5*x_6^2-15564*x_0*x_2^2*x_5*x_6^2+3135*x_1*x_2^2*x_5*x_6^2+9716*x_2^3*x_5*x_6^2-10949*x_0^2*x_3*x_5*x_6^2-2486*x_0*x_1*x_3*x_5*x_6^2+11943*x_1^2*x_3*x_5*x_6^2+1562*x_0*x_2*x_3*x_5*x_6^2-7580*x_1*x_2*x_3*x_5*x_6^2+9568*x_2^2*x_3*x_5*x_6^2+14601*x_0*x_3^2*x_5*x_6^2-8394*x_1*x_3^2*x_5*x_6^2-5951*x_2*x_3^2*x_5*x_6^2-12554*x_3^3*x_5*x_6^2+10897*x_0^3*x_6^3+13147*x_0^2*x_1*x_6^3+13368*x_0*x_1^2*x_6^3-7700*x_1^3*x_6^3-447*x_0^2*x_2*x_6^3+5550*x_0*x_1*x_2*x_6^3+1594*x_1^2*x_2*x_6^3-9440*x_0*x_2^2*x_6^3-2032*x_1*x_2^2*x_6^3-15351*x_0^2*x_3*x_6^3-900*x_0*x_1*x_3*x_6^3-1890*x_1^2*x_3*x_6^3-5935*x_0*x_2*x_3*x_6^3-426*x_1*x_2*x_3*x_6^3-15044*x_2^2*x_3*x_6^3-1568*x_0*x_3^2*x_6^3-4306*x_1*x_3^2*x_6^3-750*x_2*x_3^2*x_6^3+12819*x_3^3*x_6^3-7787*x_0^3*x_4^2*x_7-7763*x_0^2*x_1*x_4^2*x_7-8671*x_0*x_1^2*x_4^2*x_7+8914*x_1^3*x_4^2*x_7+13379*x_0^2*x_2*x_4^2*x_7-4695*x_0*x_1*x_2*x_4^2*x_7-9620*x_1^2*x_2*x_4^2*x_7+2086*x_0*x_2^2*x_4^2*x_7+6375*x_1*x_2^2*x_4^2*x_7+726*x_2^3*x_4^2*x_7-734*x_0^2*x_3*x_4^2*x_7-8898*x_0*x_1*x_3*x_4^2*x_7-15128*x_1^2*x_3*x_4^2*x_7-8230*x_0*x_2*x_3*x_4^2*x_7-6626*x_1*x_2*x_3*x_4^2*x_7+9007*x_2^2*x_3*x_4^2*x_7-3134*x_0*x_3^2*x_4^2*x_7+1531*x_1*x_3^2*x_4^2*x_7+8593*x_2*x_3^2*x_4^2*x_7+4262*x_3^3*x_4^2*x_7+14722*x_0^3*x_4*x_5*x_7-1603*x_0^2*x_1*x_4*x_5*x_7+15731*x_0*x_1^2*x_4*x_5*x_7-4107*x_1^3*x_4*x_5*x_7-10761*x_0^2*x_2*x_4*x_5*x_7+2419*x_0*x_1*x_2*x_4*x_5*x_7+9144*x_1^2*x_2*x_4*x_5*x_7-13397*x_0*x_2^2*x_4*x_5*x_7-10434*x_1*x_2^2*x_4*x_5*x_7-14098*x_2^3*x_4*x_5*x_7-5682*x_0^2*x_3*x_4*x_5*x_7+13192*x_0*x_1*x_3*x_4*x_5*x_7+379*x_1^2*x_3*x_4*x_5*x_7-8467*x_0*x_2*x_3*x_4*x_5*x_7+1807*x_1*x_2*x_3*x_4*x_5*x_7-2645*x_2^2*x_3*x_4*x_5*x_7+13386*x_0*x_3^2*x_4*x_5*x_7-4348*x_1*x_3^2*x_4*x_5*x_7+1970*x_2*x_3^2*x_4*x_5*x_7-4433*x_3^3*x_4*x_5*x_7+4966*x_0^3*x_5^2*x_7-3135*x_0^2*x_1*x_5^2*x_7+11999*x_0*x_1^2*x_5^2*x_7+15108*x_1^3*x_5^2*x_7-12419*x_0^2*x_2*x_5^2*x_7-15899*x_0*x_1*x_2*x_5^2*x_7+10436*x_1^2*x_2*x_5^2*x_7-4111*x_0*x_2^2*x_5^2*x_7-11729*x_1*x_2^2*x_5^2*x_7-3062*x_2^3*x_5^2*x_7+12480*x_0^2*x_3*x_5^2*x_7+6521*x_0*x_1*x_3*x_5^2*x_7+2394*x_1^2*x_3*x_5^2*x_7-15348*x_0*x_2*x_3*x_5^2*x_7-12779*x_1*x_2*x_3*x_5^2*x_7+15266*x_2^2*x_3*x_5^2*x_7+15740*x_0*x_3^2*x_5^2*x_7-3214*x_1*x_3^2*x_5^2*x_7-16163*x_2*x_3^2*x_5^2*x_7-591*x_3^3*x_5^2*x_7+11510*x_0^3*x_4*x_6*x_7+8987*x_0^2*x_1*x_4*x_6*x_7-1312*x_0*x_1^2*x_4*x_6*x_7+11868*x_1^3*x_4*x_6*x_7+11472*x_0^2*x_2*x_4*x_6*x_7+7195*x_0*x_1*x_2*x_4*x_6*x_7-12517*x_1^2*x_2*x_4*x_6*x_7+3466*x_0*x_2^2*x_4*x_6*x_7+8070*x_1*x_2^2*x_4*x_6*x_7-6390*x_2^3*x_4*x_6*x_7-5818*x_0^2*x_3*x_4*x_6*x_7-1539*x_0*x_1*x_3*x_4*x_6*x_7+9507*x_1^2*x_3*x_4*x_6*x_7+2545*x_0*x_2*x_3*x_4*x_6*x_7+13367*x_1*x_2*x_3*x_4*x_6*x_7-9350*x_2^2*x_3*x_4*x_6*x_7-8337*x_0*x_3^2*x_4*x_6*x_7-5656*x_1*x_3^2*x_4*x_6*x_7+15682*x_2*x_3^2*x_4*x_6*x_7+9813*x_3^3*x_4*x_6*x_7-10509*x_0^3*x_5*x_6*x_7-7639*x_0^2*x_1*x_5*x_6*x_7+7893*x_0*x_1^2*x_5*x_6*x_7-5817*x_1^3*x_5*x_6*x_7-11636*x_0^2*x_2*x_5*x_6*x_7+1954*x_0*x_1*x_2*x_5*x_6*x_7-7734*x_1^2*x_2*x_5*x_6*x_7+10721*x_0*x_2^2*x_5*x_6*x_7+11830*x_1*x_2^2*x_5*x_6*x_7-10407*x_2^3*x_5*x_6*x_7-14100*x_0^2*x_3*x_5*x_6*x_7-12123*x_0*x_1*x_3*x_5*x_6*x_7+2237*x_1^2*x_3*x_5*x_6*x_7+3823*x_0*x_2*x_3*x_5*x_6*x_7+2298*x_1*x_2*x_3*x_5*x_6*x_7-1163*x_2^2*x_3*x_5*x_6*x_7+12089*x_0*x_3^2*x_5*x_6*x_7-11203*x_1*x_3^2*x_5*x_6*x_7+1605*x_2*x_3^2*x_5*x_6*x_7+14602*x_3^3*x_5*x_6*x_7-13945*x_0^3*x_6^2*x_7+6999*x_0^2*x_1*x_6^2*x_7-12079*x_0*x_1^2*x_6^2*x_7-12507*x_1^3*x_6^2*x_7-9565*x_0^2*x_2*x_6^2*x_7+13749*x_0*x_1*x_2*x_6^2*x_7-8397*x_1^2*x_2*x_6^2*x_7+10170*x_0*x_2^2*x_6^2*x_7+12253*x_1*x_2^2*x_6^2*x_7+15044*x_2^3*x_6^2*x_7-14361*x_0^2*x_3*x_6^2*x_7-15354*x_0*x_1*x_3*x_6^2*x_7-15407*x_1^2*x_3*x_6^2*x_7-5863*x_0*x_2*x_3*x_6^2*x_7+11301*x_1*x_2*x_3*x_6^2*x_7-15831*x_2^2*x_3*x_6^2*x_7-9629*x_0*x_3^2*x_6^2*x_7-8489*x_1*x_3^2*x_6^2*x_7-11875*x_2*x_3^2*x_6^2*x_7-283*x_3^3*x_6^2*x_7-13953*x_0^3*x_4*x_7^2-11702*x_0^2*x_1*x_4*x_7^2+12956*x_0*x_1^2*x_4*x_7^2-13315*x_1^3*x_4*x_7^2-3740*x_0^2*x_2*x_4*x_7^2-2424*x_0*x_1*x_2*x_4*x_7^2-10341*x_1^2*x_2*x_4*x_7^2+3081*x_0*x_2^2*x_4*x_7^2+5308*x_1*x_2^2*x_4*x_7^2-3219*x_2^3*x_4*x_7^2-15533*x_0^2*x_3*x_4*x_7^2-12298*x_0*x_1*x_3*x_4*x_7^2-1011*x_1^2*x_3*x_4*x_7^2+137*x_0*x_2*x_3*x_4*x_7^2-4424*x_1*x_2*x_3*x_4*x_7^2-11406*x_2^2*x_3*x_4*x_7^2-29*x_0*x_3^2*x_4*x_7^2-4822*x_1*x_3^2*x_4*x_7^2+9460*x_2*x_3^2*x_4*x_7^2-6274*x_3^3*x_4*x_7^2-10151*x_0^3*x_5*x_7^2-3693*x_0^2*x_1*x_5*x_7^2+1971*x_0*x_1^2*x_5*x_7^2-8035*x_1^3*x_5*x_7^2+2996*x_0^2*x_2*x_5*x_7^2-12901*x_0*x_1*x_2*x_5*x_7^2+15021*x_1^2*x_2*x_5*x_7^2-2591*x_0*x_2^2*x_5*x_7^2-3637*x_1*x_2^2*x_5*x_7^2-1618*x_2^3*x_5*x_7^2+13930*x_0^2*x_3*x_5*x_7^2+2753*x_0*x_1*x_3*x_5*x_7^2-5016*x_1^2*x_3*x_5*x_7^2-3473*x_0*x_2*x_3*x_5*x_7^2+1300*x_1*x_2*x_3*x_5*x_7^2+1978*x_2^2*x_3*x_5*x_7^2+9553*x_0*x_3^2*x_5*x_7^2-1497*x_1*x_3^2*x_5*x_7^2-585*x_2*x_3^2*x_5*x_7^2+15646*x_3^3*x_5*x_7^2-1416*x_0^3*x_6*x_7^2-15928*x_0^2*x_1*x_6*x_7^2+1406*x_0*x_1^2*x_6*x_7^2+4616*x_1^3*x_6*x_7^2-6859*x_0^2*x_2*x_6*x_7^2-8497*x_0*x_1*x_2*x_6*x_7^2+14972*x_1^2*x_2*x_6*x_7^2-5987*x_0*x_2^2*x_6*x_7^2-8932*x_1*x_2^2*x_6*x_7^2-16168*x_2^3*x_6*x_7^2-10462*x_0^2*x_3*x_6*x_7^2-8641*x_0*x_1*x_3*x_6*x_7^2-14497*x_1^2*x_3*x_6*x_7^2-406*x_0*x_2*x_3*x_6*x_7^2-525*x_1*x_2*x_3*x_6*x_7^2-7586*x_2^2*x_3*x_6*x_7^2-8952*x_0*x_3^2*x_6*x_7^2-11721*x_1*x_3^2*x_6*x_7^2-9970*x_2*x_3^2*x_6*x_7^2+543*x_3^3*x_6*x_7^2+7739*x_0^3*x_7^3-11767*x_0^2*x_1*x_7^3+2857*x_0*x_1^2*x_7^3+11834*x_1^3*x_7^3+6195*x_0^2*x_2*x_7^3+10119*x_0*x_1*x_2*x_7^3+12793*x_1^2*x_2*x_7^3-8870*x_0*x_2^2*x_7^3-7258*x_1*x_2^2*x_7^3+6642*x_2^3*x_7^3-4233*x_0^2*x_3*x_7^3-6407*x_0*x_1*x_3*x_7^3-75*x_1^2*x_3*x_7^3-3427*x_0*x_2*x_3*x_7^3+2148*x_1*x_2*x_3*x_7^3+10253*x_2^2*x_3*x_7^3+6274*x_0*x_3^2*x_7^3-11387*x_1*x_3^2*x_7^3-543*x_2*x_3^2*x_7^3,0,9215*x_0+13986*x_1+8628*x_2-4866*x_3+1,8703*x_4-8035*x_5+2841*x_6-10261*x_7+1,7130*x_1*x_4*t+15188*x_2*x_4*t-4327*x_3*x_4*t-7130*x_0*x_5*t+9498*x_2*x_5*t+13579*x_3*x_5*t-15188*x_0*x_6*t-9498*x_1*x_6*t+15519*x_3*x_6*t+4327*x_0*x_7*t-13579*x_1*x_7*t-15519*x_2*x_7*t+6)



///

