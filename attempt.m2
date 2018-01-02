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
   "ChowRing",
   "MultiProjCoordRing",
   "isMultiHomogeneous",
   "Segre", 
   "makeMultiHom1",
   "makeMultiHom2",
   "HomMethod", 
   "ProjDegMethod",
   "SloppinessLevel",
   "Sparsity",
   "semirandom", 
   "eXYmult"

}
needsPackage "NumericalAlgebraicGeometry";
eXYmult=method(TypicalValue=>ZZ,Options => {HomMethod=>1,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4});
eXYmult (Ideal,Ideal):=opts->(I1,I2)->(
    print "eXYmult(I,J) computes e_XY where X is the top equidimensional component of V(I) and Y=V(J) (Y is assumed to be irreducible)";
    md:=multidegree (I1+I2);
    A:=ChowRing(ring(I2));
    clX:=sub(md,matrix{gens(A)});
    seg:= Segre(I1,I2,A,HomMethod=>opts.HomMethod,ProjDegMethod=>opts.ProjDegMethod,SloppinessLevel=>opts.SloppinessLevel,Sparsity=>opts.Sparsity);
    mons:=flatten entries monomials clX;
    segMons:=sum(for m in mons list m*seg_(m));
    <<"[X]= "<<clX<<" these monomials in Segre class= "<<segMons<<endl;
    return lift(segMons//clX,ZZ);
    );

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

semirandomCoeff = () -> (
    ps := {0,0,0,7,5,3,2,-2,-3,-5,-7};
    return ps_(random(0,length(ps)-1))
)

--semirandom = (deg,R) -> (
--     if #deg =!= degreeLength R then error ("expected length of degree vector to be ", degreeLength R);
--     k := coefficientRing R;
--     m := basis(deg, R);
--     if m == 0 then 0_R else (
--          n := matrix table(numgens source m,1, x -> promote(semirandomCoeff(),R));
 --         (m*n)_(0,0)
--     )
-- )
semirandom =method(TypicalValue=>RingElement,Options => {Sparsity=>2});

semirandom (List,Ring,ZZ):=opts->(deg,R,Spar)->(
    kk := coefficientRing R;
    --Spar:=opts.Sparsity;
    randPoly:=0;
    NumZeros:=0;
    sparList:={};
    if char(kk)==0 then(
	fmon:=flatten entries monomials random(deg,R);
	NumZeros=ceiling(Spar/10*length(fmon));
	sparList=random(join(for i from 1 to NumZeros list 0, for j from 1 to length(fmon)-NumZeros list (-1)^(random(0,9))*random(1,300)/random(1,20)));
	randPoly=sum(0..length(fmon)-1, i->sparList_i*fmon_i);
	)
    else(
	--fterm:=terms random(deg, R);
	fterm:=flatten entries monomials random(deg,R);
	NumZeros=ceiling(Spar/10*length(fterm));
	sparList=random(join(for i from 1 to NumZeros list 0, for j from 1 to length(fterm)-NumZeros list (-1)^(random(0,9))*random(1,300)));
	randPoly=sum(0..length(fterm)-1, i->sparList_i*fterm_i);
	);
    return randPoly;
    );
semirandom (List,Ring):=opts->(deg,R)-> (
     if #deg =!= degreeLength R then error ("expected length of degree vector to be ", degreeLength R);
     k := coefficientRing R;
     m := basis(deg, R);
     if m == 0 then 0_R else (
          n := matrix table(numgens source m,1, x -> promote(semirandomCoeff(),R));
         (m*n)_(0,0)
	      )
);

makeMultiHom1=method(TypicalValue=>Ideal);
makeMultiHom1 Ideal:=I->(
    -- print("makeMultiHom1 starting ideal: " | netList flatten entries gens I);
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
    J:= for i from 1 to n list sum(gensI,g -> g*semirandom(maxDegs-degree(g),R));
    -- print("makeMultiHom1 returned ideal: " | netList J);
    return ideal J;
    );
makeMultiHom2=method(TypicalValue=>Ideal);
makeMultiHom2 (Ideal,Ideal,ZZ):=(K,J,dimY)->(
    I:=K+J;
    R:=ring I;
    deglenR:=degreeLength R;
    degs:=unique degrees R;
    n:=numgens(R)-length(degs);
    kk:=coefficientRing R;
    gensI:= delete(0_R,flatten sort entries gens K);
    homGens:={};
    exmon:=0;
    degI:= degrees I;
    m:=length unique degrees R;
    transDegI:= transpose degI;
    len:= length transDegI;
    maxDegs:= for i from 0 to len-1 list max transDegI_i;
    tempId:={};
    PDl:={};
    curIrel:=0;
    degDif:=0;
    tempfGens:=0;
    --print "start pdl";
    pdlHashList:={};
    for d in degs do(
	tempId={};
	for y in gens(R) do(
	    if degree(y)==d then(
		tempId=append(tempId,y);
		);
	    );
	pdlHashList=append(pdlHashList,{d,tempId});
	PDl=append(PDl,tempId);
	);
    --print "done setup";
    --<<{degs,PDl}<<endl;
    irelHash:=hashTable(pdlHashList);
    --print "main loop start ";
    --<<peek(irelHash)<<endl;
    for f in gensI do(
	if degree(f)==maxDegs then(
	    homGens=append(homGens,f);
	    )
	else(
	    degDif=maxDegs-degree(f);
	    tempfGens=ideal(f);
	    for i from 0 to #degDif-1 do(
		curIrel=irelHash#(OneAti(deglenR,i));
		tempfGens=tempfGens*ideal(for g in curIrel list g^(degDif_i));
		);
	    homGens=join(homGens,flatten entries gens tempfGens);
	    );
	);
    return ideal for j from 0 to dimY list sum(homGens,l->l*random(kk)*random(0,4));
    --return ideal homGens;
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

Segre=method(TypicalValue => RingElement,Options => {HomMethod=>2,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4}); 
Segre (Ideal,Ideal) :=opts-> (I1,I2) -> ( 
    --print "start segre wrapper";
    A:=ChowRing(ring(I2));
    return Segre(I1,I2,A,HomMethod=>opts.HomMethod,ProjDegMethod=>opts.ProjDegMethod,SloppinessLevel=>opts.SloppinessLevel,Sparsity=>opts.Sparsity);
    );

Segre (Ideal,Ideal,QuotientRing) :=opts->(X,Y,A) -> (
    --print "start segre";
    <<"ProjDegMethod= "<<opts.ProjDegMethod<<endl;
    if not isMultiHomogeneous(X) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHomogeneous(Y) then (print "the second ideal is not multi-homogenous, please correct this"; return 0;);
    Rx:=ring X;
    Ry:=ring Y;
    kk:=coefficientRing Ry;
    if opts.ProjDegMethod=="NAG" and char(kk)!=0 then (print "Use QQ for NAG"; return 0;);
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
    t:=symbol t;
    if opts.ProjDegMethod=="AdjT" then(
    	R:=kk[gens Ry,t];
	)
    else(
	R=Ry;
	);
    --n is (projective) dimension of ambient space
    --n:=numgens(Ry) -1;
    --find gb's
    gbXonly := ideal groebnerBasis(X, Strategy=>"MGB");
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
    <<"[Y]= "<<clY<<endl<<", alpha= "<<alpha<<endl;
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
	    if opts.HomMethod==1 then (
		Wg=flatten entries gens (makeMultiHom1(W)+Ls);
		)
	    else(
		Wg=flatten entries gens (makeMultiHom2(X,Y,dimY)+Ls);
		);
	    --Wg=flatten entries gens homogenate(W+Ls);
	    G=ideal(for j from 1 to dimY-i list sum(Wg,g->random(kk)*g));
	    --<<"G= "<<G<<endl;
	    --G=saturate (G,product(PDl));
	    --<<"G= "<<G<<endl;
	    for p in PDl do (
		LA=LA+sub(ideal(1-sum(numgens(p),i->random(kk)*p_i)),Ry);
		);
	    if opts.ProjDegMethod=="Sat" then(
		--pd = degree saturate(Y+Ls+G,ideal(sum(numgens(W),j->random(kk)*W_j)));
		pd = degree saturate(Y+Ls+G,ideal(X_0));
		--pd = degree saturate(Y+Ls+G+LA,X);
		)
	    --else if(opts.ProjDegMethod=="sub1") then(
	--	pd=degree(Y+Ls+G+LA)-degree(Y+Ls+G+LA+X);
	--	)
	  --  else if(opts.ProjDegMethod=="sub2") then(
	--	ZeroDimGB=groebnerBasis(Y+Ls+G+LA, Strategy=>"F4");
	--	<<"dim= "<<dim(ideal(ZeroDimGB))<<endl;
	--	Zdgb2:=groebnerBasis(ideal(ZeroDimGB)+gbXonly, Strategy=>"F4");
	--	pd=(numColumns basis(cokernel leadTerm ZeroDimGB))-(numColumns basis(cokernel leadTerm Zdgb2));
	--	)
	    else if(opts.ProjDegMethod=="NAG") then(
		Sys:=flatten entries gens(Y+Ls+G+LA);
		sols:=solveSystem Sys;
		Fsys:=flatten entries gens W;
		--for s in sols
		badsols:=0;
		temp:=true;
		for s in sols do(
		    temp=true;
		    for f in Fsys do(
			if sub(f,matrix{coordinates s})>1e-10 then temp=false;
			);
		    if temp==true then badsols=badsols+1;
		    );
		pd=#sols-badsols;
		)
	    else(
	    	--<<"w= "<<w<<",Ls= "<<Ls<<<<",LA= "<<(LA)<<endl;
		--EqT=ideal( sum((numgens W),j->(1-t*random(kk)*substitute(W_j,R))));
	    	EqT=ideal( 1-t*sum((numgens X),j->(random(kk)*substitute(X_j,R))));
		--EqT=ideal(1-t*substitute(X_0,R));
	    	--print "start gb";
	    	--print(toString(sub(Y+Ls+G+LA,R)+EqT));
	    	--saturate(Y+G,W)
		--<<"deg big = "<<degree(Y+Ls+G+LA)<<", deg little= "<<degree(Y+Ls+G+LA+X)<<endl;
		ZeroDimGB=groebnerBasis(sub(Y+Ls+G+LA,R)+EqT, Strategy=>"F4");
	    	--<<"dim= "<<dim(ideal(ZeroDimGB))<<" numgens G "<<numgens(G)<<", codim G= "<<codim(G)<<<<", codim Ls= "<<codim(Ls)<<endl;
            	--<<"G= "<<G<<",Ls= "<<Ls<<<<",LA= "<<(LA)<<endl;
	    	pd=numColumns basis(cokernel leadTerm ZeroDimGB);
		);
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

end

TEST ///
{*  
    restart
    needsPackage "attempt"
*} 
  
restart
needsPackage "attempt"
R=MultiProjCoordRing({6})
x=gens(R)
degrees R
I=ideal(random(2,R),x_0^4-x_1*x_3^3-x_4*x_5^3)
J=ideal(x_0*x_2-x_4*x_5)
time Segre(I,J,HomMethod=>2) 
eXYmult(I,J)


needsPackage "NumericalAlgebraicGeometry";
R = CC[x,y,z];
F = {x^2+y^2+z^2-1, y-x^2, z-x^3};
sol = solveSystem F 
goodsols=0
temp=true;
for s in sol do(
    temp=true;
    for f in F do(
	if sub(f,matrix{coordinates s})>1e-10 then temp=false;
	);
    if temp==true then goodsols=goodsols+1;
    );
goodsols
#sol
sub(F_0,matrix{coordinates first sol})
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
R=MultiProjCoordRing(QQ,{2,3})
x=gens(R)
I=ideal(x_0*x_1*x_5-x_2^2*x_6)
J=ideal(x_0)
time Segre(J,I,ProjDegMethod=>"Sat");
time Segre(J,I)
time Segre(J,I,ProjDegMethod=>"NAG");
restart
-- test in a normal projective space
needsPackage "attempt"
needsPackage "FMPIntersectionTheory"
PP3 = QQ[x,y,z,t]
Y = ideal "xy-zt"
X = ideal random(4,PP3)
Segre(X,Y) 
Segre(X,Y,ProjDegMethod=>"Sat") 
Segre(X,Y,ProjDegMethod=>"NAG") 


restart
-- point on a line
needsPackage "attempt"
R = MultiProjCoordRing({1,1})
x=gens R
Y=ideal(x_0*x_3-x_1*x_2)
X=ideal(x_0^2*x_3-x_1^2*x_2)
X1=ideal(X_0*random({1,2},R))
saturate(5*X+Y,X)
degree saturate(saturate(X1+Y,X),ideal(x_0,x_1)*ideal(x_2,x_3))
time Segre(X, Y)
time Segre(ideal(x_0-x_1)+, D,ProjDegMethod=>"NAG")
-- s(PP0,PP1) = [PP0]

-- union of coordinate axes in PP3 (diagonal)
needsPackage "attempt"
R = MultiProjCoordRing({3,3})
x = gens(R)
D = minors(2,matrix{{x_0..x_3},{x_4..x_7}})
X = ideal(x_0*x_1,x_1*x_2,x_0*x_2)
time Segre(X,D,HomMethod=>1)
-- s(axes,PP3) = 3[PP1] - 10[PP0] ... I think this means 3 *("both" PP1's)

Z=D
kk=coefficientRing R
S=R/Z
I1=sub(ideal for j from 1 to 3 list sum(flatten entries gens X, l->random(kk)*l),S)
K1=saturate(I1,sub(X,S))
J1=saturate (K1,ideal(S_0,S_1,S_2,S_3)*ideal(S_4..S_7))
degree J1



multidegree (X+D)
degrees X
-- i.e. h^3h_2^2 and h^2h_2^3
restart
needsPackage "attempt"
R = MultiProjCoordRing({3,4})
semirandom({1,1},R)
x=gens R
degrees R
I=ideal(x_0*x_6^2-x_1*x_5*x_7,x_0*x_5-8*x_1*x_6+3*x_2*x_4)
J=ideal random({1,1},R)
time Segre(I,J,ProjDegMethod=>"Sat")
seg=time Segre(I,J)

eXYmult(I,J)
md=multidegree(I+J)
md=multidegree ideal(random({2,0},R))
A=ChowRing(R)
clX=sub(md,matrix{gens(A)})
mons=flatten entries monomials clX
sum(for m in mons list m*seg_(m))//clX
te=terms multidegree ideal(random({2,0},R))
exponents te_0
restart
needsPackage "attempt"
kk=ZZ/32749
R = kk[x,y,z,t]
PP3xPP3 = MultiProjCoordRing(kk,{3,3})
m1 = map(PP3xPP3,R,take(gens PP3xPP3,4))
m2 = map(PP3xPP3,R,drop(gens PP3xPP3,4))
f = ideal "x(x2-2xy+zt) + y(x2-3yt+z2+3t2-3tz+xy)"
h = ideal "x(x2-7y2-zt) + y(3x2-5yt)"
X = m1(f)
Y = m2(h)
D = minors(2,matrix{take(gens PP3xPP3,4),drop(gens PP3xPP3,4)})
X+Y
time Segre(D, X+Y,HomMethod=>2)
time Segre(D, X+Y,ProjDegMethod=>"Sat")
R = ZZ/32003[x,y,z,w];
P = ideal "  yw-z2,   xw-yz"
I = ideal "z(yw-z2)-w(xw-yz), xz-y2"
Segre(P,I)
time eXYmult(P,I)
P=ideal (x,y)
I
restart
needsPackage "attempt"
R = QQ[x,y,z];
I=ideal(x^5+y^5+z^5)
P=ideal(z)
Segre(P,I)


restart
needsPackage "LocalRings"
R = QQ[x,y,z];
I=ideal(x^5+y^5+z^5)
P=ideal(z,y)
RP = localRing(R, P);
M = RP^1/promote(I, RP)
elapsedTime length(RP^1/promote(I, RP))

restart
needsPackage "LocalRings"
R = QQ[x,y,z,w];
I = ideal (y*w-z^2,x*w-y*z,  x*z-y^2)
J = ideal (z*(y*w-z^2)-w*(x*w-y*z), x*z-y^2)
isSubset(J,I)

P=ideal(random(3,R),random(3,R))
I=ideal(z*P_0+w*P_1)+P
codim I == codim P --Hence this is finite, thus I is artinian in R_P, i.e. RP/IP is an artinian ring.
isPrime P
RP = localRing(R, P)
N = RP^1/promote(I, RP)
time length(N)
isSubset(I,P)
I==P
time for i from 0 to 3 list hilbertSamuelFunction(N, i)
isPrimary I
restart
needsPackage "LocalRings"
R = QQ[x,y,z];
RP = localRing(R, ideal(x));
I=ideal(x^5+y^5+z^5,z^5+y^5)
M = RP^1/I
elapsedTime length(RP^1/I) -- 0.5 seconds
elapsedTime (for i from 0 to 6 list hilbertSamuelFunction(M, i)) -- 5.5 seconds

elapsedTime assert((for i from 0 to 6 list hilbertSamuelFunction(promote(max ring M, ring M),M, i))//sum == 27)


x=gens R
J
{*  
    restart
    needsPackage "attempt"
*} 
kk=ZZ/32749
R = MultiProjCoordRing(kk,{2,3})
x=(gens R)_{0..2}
y=(gens R)_{3..6}
I=ideal(x_0^2*x_1*y_1^2-x_0^3*y_0*y_3)
J=ideal(x_1^2*x_0*y_3^2-x_0^3*y_2*y_0-x_0^3*y_0^2)    
time seg=Segre(I,J,HomMethod=>2)
decompose (I+J)
multidegree(I+J)

R=MultiProjCoordRing({2,1})
x=(gens R)_{0..2}
y=(gens R)_{3..4}
I=ideal(random({1,0},R),random({1,0},R))
B=ideal(y_0*I_1-y_1*I_0)
E=?

R=MultiProjCoordRing({3,3})
x=(gens(R))_{0..3}
y=(gens(R))_{4..7}
Qx=random({2,0},R)
Qy=sub(Qx,matrix{join(y,for i from 4 to 7 list 0)})
D = minors(2,matrix{x,y})
I=ideal(Qx,Qy,D)
Cx=random({1,0},R)
Cy=sub(Cx,matrix{join(y,for i from 4 to 7 list 0)})
C=ideal(Cx,Cy)
Segre(C,I)


TEST ///
{*  INT PRODUCT OF CUBIC SURFACES
    restart
    needsPackage "attempt"
*} 
kk=ZZ/32749
R = kk[x,y,z,t]
PP3xPP3 = MultiProjCoordRing(kk,{3,3})
m1 = map(PP3xPP3,R,take(gens PP3xPP3,4))
m2 = map(PP3xPP3,R,drop(gens PP3xPP3,4))
f = ideal "x(x2-2xy+zt) + y(x2-3yt+z2+3t2-3tz+xy)"
h = ideal "x(x2-7y2-zt) + y(3x2-5yt)"
g = ideal "x(23xy-34z2-17yt+t2) + y(x2+y2+z2+xy+zt)"
X = m1(f+g)
Y = m2(h+g)
D = minors(2,matrix{take(gens PP3xPP3,4),drop(gens PP3xPP3,4)})
time Segre(D,X+Y,HomMethod=>2)

Z=X+Y
S=PP3xPP3/Z
I1=sub(ideal for j from 1 to 4 list sum(flatten entries gens D, l->random(kk)*l),S)
K1=saturate(I1,sub(D,S))
J1=saturate (K1,ideal(S_0,S_1,S_2,S_3)*ideal(S_4..S_7))
degree J1

X+Y
Y=X+Y
X=D
     Rx=ring X
    Ry=ring Y
    kk=coefficientRing Ry
A=ChowRing(Ry)
    B=flatten entries sort basis A
    degs=unique degrees Ry
      tempId={};
    PDl={};
    for d in degs do(
	tempId={};
	for y in gens(Ry) do(
	    if degree(y)==d then(
		tempId=append(tempId,y);
		);
	    );
	PDl=append(PDl,ideal(tempId));
	);
    X=saturate(X,product(PDl))
    Y=saturate(Y,product(PDl))
    n=numgens(Ry)-length(degs)
    --find the max multidegree, write it as a class alpha
    degX= degrees (X+Y)
    transDegX= transpose degX
    len= length transDegX
    maxDegs= for i from 0 to len-1 list max transDegX_i
    deg1B:={};
    for w in B do if sum(degree(w))==1 then deg1B=append(deg1B,w)
    m=length degs
    alpha=sum(length deg1B,i->(basis(OneAti(m,i),A))_0_0*maxDegs_i) 
    zdim=0
    for b in B do(
	if sum(flatten(exponents(b)))==n then zdim=b;
	);
    seg=0;

    t=symbol t;
    if opts.ProjDegMethod=="AdjT" then(
    	R=kk[gens Ry,t];
	)
    else(
	R=Ry;
	);
    --n is (projective) dimension of ambient space
    --n:=numgens(Ry) -1;
    --find gb's
    gbXonly = ideal groebnerBasis(X, Strategy=>"MGB")
    gbX = groebnerBasis(X+Y, Strategy=>"MGB")
    gbY = groebnerBasis(Y, Strategy=>"MGB")
    codimX = codim ideal leadTerm gbX
    codimY= codim ideal leadTerm gbY
    dimX = n-codimX
    dimY= n-codimY
    --Degree only depends on the leading monomials of a GB
    --degY:=degree monomialIdeal gbY;
    c={};
    v=0;
    Ls=0;
    ve=0;
    ZeroDimGB=0;
    LA=0;
    clY=0;
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
    <<"[Y]= "<<clY<<", alpha= "<<alpha<<endl;
    --print "end compute class Y";
    --degY*h^(n-dimY);
    -- V \subset |O(d)| is the linear system on Y for which X is the base scheme
    -- in reality, it's the largest degree among the generators of (X + Y)
    --d := first degree( (gens homogenate(X+Y))_(0,0) );
    W=X+Y
    Wg=0
    G=0;
    pd=0;
    EqT=0;
    c={};
    projectiveDegreesList = {};
i=0
    for i from 0 to dimX do (
	c={};
    	for w in B do if sum(flatten(exponents(w)))==n-i then c=append(c,w);
w=first c
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
	    if opts.HomMethod==1 then (
		Wg=flatten entries gens makeMultiHom1(W+Ls);
		)
	    else(
		Wg=flatten entries gens makeMultiHom1(W+Ls);
		);
	    --Wg=flatten entries gens homogenate(W+Ls);
	    G=ideal(for j from 1 to dimY-i list sum(Wg,g->random(kk)*g));
	    <<"G= "<<G<<endl;
	    --G=saturate (G,product(PDl));
	    --<<"G= "<<G<<endl;
	    for p in PDl do (
		LA=LA+sub(ideal(1-sum(numgens(p),i->random(kk)*p_i)),Ry);
		);
	    if opts.ProjDegMethod=="Sat" then(
		--pd = degree saturate(Y+Ls+G,ideal(sum(numgens(W),j->random(kk)*W_j)));
		pd = degree saturate(Y+Ls+G,ideal(X_0));
		--pd = degree saturate(Y+Ls+G+LA,X);
		)
	    --else if(opts.ProjDegMethod=="sub1") then(
	--	pd=degree(Y+Ls+G+LA)-degree(Y+Ls+G+LA+X);
	--	)
	  --  else if(opts.ProjDegMethod=="sub2") then(
	--	ZeroDimGB=groebnerBasis(Y+Ls+G+LA, Strategy=>"F4");
	--	<<"dim= "<<dim(ideal(ZeroDimGB))<<endl;
	--	Zdgb2:=groebnerBasis(ideal(ZeroDimGB)+gbXonly, Strategy=>"F4");
	--	pd=(numColumns basis(cokernel leadTerm ZeroDimGB))-(numColumns basis(cokernel leadTerm Zdgb2));
	--	)
	    else if(opts.ProjDegMethod=="NAG") then(
		Sys:=flatten entries gens(Y+Ls+G+LA);
		sols:=solveSystem Sys;
		Fsys:=flatten entries gens W;
		--for s in sols
		badsols:=0;
		temp:=true;
		for s in sols do(
		    temp=true;
		    for f in Fsys do(
			if sub(f,matrix{coordinates s})>1e-10 then temp=false;
			);
		    if temp==true then badsols=badsols+1;
		    );
		pd=#sols-badsols;
		)
	    else(
	    	--<<"w= "<<w<<",Ls= "<<Ls<<<<",LA= "<<(LA)<<endl;
		--EqT=ideal( sum((numgens W),j->(1-t*random(kk)*substitute(W_j,R))));
	    	EqT=ideal( sum((numgens X),j->(1-t*random(kk)*substitute(X_j,R))));
		--EqT=ideal(1-t*substitute(X_0,R));
	    	--print "start gb";
	    	--print(toString(sub(Y+Ls+G+LA,R)+EqT));
	    	--saturate(Y+G,W)
		--<<"deg big = "<<degree(Y+Ls+G+LA)<<", deg little= "<<degree(Y+Ls+G+LA+X)<<endl;
	    	ZeroDimGB=groebnerBasis(sub(Y+Ls+G+LA,R)+EqT, Strategy=>"F4");
	    	--<<"dim= "<<dim(ideal(ZeroDimGB))<<", codim G= "<<codim(G)<<<<", codim Ls= "<<codim(Ls)<<endl;
            	--<<"G= "<<G<<",Ls= "<<Ls<<<<",LA= "<<(LA)<<endl;
	    	pd=numColumns basis(cokernel leadTerm ZeroDimGB);
		);
	    --<<"w= "<<w<<", pd= "<<pd<<endl;
            projectiveDegreesList = append(projectiveDegreesList,pd*w);
	    );
	);
     <<"Projective degrees= "<<projectiveDegreesList<<endl;
    Gam:=sum(projectiveDegreesList);
 ///