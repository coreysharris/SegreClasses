newPackage( "EffIntThy",
    Version =>"0.2",
    Date => "Jan 3, 2018",
    Authors => {
        {Name => "Martin Helmer",
         Email => "martin.helmer@berkeley.edu",
         HomePage => "http://martin-helmer.com"},
        {Name => "Corey Harris",
         Email => "Corey.Harris@mis.mpg.de",
         HomePage => "http://coreyharris.name"}
    },
    Headline => "Computes s(X,Y) in  A*(P^n1x...xP^nm)",
    PackageImports => {"NumericalAlgebraicGeometry"},
    DebuggingMode => false,
    Reload => true
);

export {
   "ChowRing",
   "MultiProjCoordRing",
   "isMultiHomogeneous",
   "Segre",
   "projectiveDegree",
   "makeMultiHom",
   "HomMethod",
   "ProjDegMethod",
   "SloppinessLevel",
   "Sparsity",
   "CompMethod",
   "eXYmult",
   "chowClass"
}

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

Scheme = new Type of MutableHashTable
globalAssignment Scheme

toString Scheme := net Scheme := X -> (
    if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
    else "a scheme")
Scheme#{Standard,AfterPrint} = X -> (
    << concatenate(interpreterDepth:"o") << lineNumber << " : "
    -- << "a projective scheme in PP^" << dim(X.AmbientSpace) << " defined by " << X.Ideal << endl;
)

scheme = method(TypicalValue => Scheme, Options => {
    -- SuperScheme => null,  -- a Scheme containing the one we are defining
    --                                           -- If I is the ideal of SuperScheme in R, and we define our
    --                                           -- new scheme with J in R, we instead will use I+J
    -- AmbientSpace => null, -- the projective space where we will be computing
    -- MakeBaseOfLinearSystem => false   -- if true, the ideal used to define the projective scheme should be made to have all terms of same degree
})
scheme Ideal :=  opts -> I -> (
    return new Scheme from {
        global ideal => I,
        global ring => ring I,
        -- global equations => eqs,
        global gb => null,
        global dim => null,
        global codim => null,
        global chowClass => null
    }
)

ideal Scheme := X -> ( X.ideal )

codim Scheme := X -> (
    if X.codim==null then ( X.codim = codim ideal leadTerm gb(X) );
    return X.codim
)

gb Scheme := opts -> X -> (
    if X.gb==null then ( X.gb = groebnerBasis(X,opts) );
    return X.gb
)

ring Scheme := X -> ( X.ring )

dim Scheme := X -> (
    if X.dim==null then (
        ambientDim := numgens(ring X) - #(unique degrees ring X);
        X.dim = ambientDim - codim X
    );
    return X.dim
)

projectiveDegree = method(TypicalValue => RingElement,Options => {HomMethod=>2,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4,Verbose=>false});
projectiveDegree (Ideal,Ideal,List) :=opts-> (I1,I2,ChowElandDim) -> (
    if opts.Verbose then print "TODO Write Wrapper, not done";
    return 0;
);
projectiveDegree(Ideal, Ideal,List,MutableHashTable) := opts-> (X,Y,ChowElandDim,Info) -> (
    --<<"ProjDegMethod= "<<opts.ProjDegMethod<<endl;
    Ry:=Info#"R";
    w:=first ChowElandDim;
    i:=last ChowElandDim;
    kk:=coefficientRing(Ry);
    t:=symbol t;
    R:=kk[gens Ry,t];
    Ls:=0;
    LA:=0;
    zdim:=Info#"zdim";
    m:=Info#"m";
    v:=zdim//w;
    dimY:=Info#"dimY";
    pd:=0;
    ve:=flatten exponents(v);
    for i from 0 to length(ve)-1 do (
        if ve_i!=0 then (
            Ls=Ls+sum(ve_i,j->ideal(random(OneAti(m,i),Ry)));
        );
    );
    Wg:=flatten entries gens (makeMultiHom(X,Y,Info)+Ls);
    G:=ideal(for j from 1 to dimY-i list sum(Wg,g->random(kk)*g));
    for p in Info#"PDl" do (
        LA=LA+sub(ideal(1-sum(numgens(p),i->random(kk)*p_i)),Ry);
    );
    if opts.ProjDegMethod=="Sat" then (
        pd = degree saturate(Y+Ls+G+LA,X);
    )
    else if(opts.ProjDegMethod=="NAG") then (
        Sys:=flatten entries gens(Y+Ls+G+LA);
        sols:=solveSystem Sys;
        Fsys:=flatten entries gens (X+Y);
        badsols:=0;
        temp:=true;
        for s in sols do (
            temp=true;
            for f in Fsys do (
                if sub(f,matrix{coordinates s})>1e-10 then temp=false;
            );
            if temp==true then badsols=badsols+1;
        );
        pd=#sols-badsols;
    ) else (
        --Defualt Method
        --print "default used";
        EqT:=ideal( 1-t*sum((numgens X),j->(random(kk)*substitute(X_j,R))));
        ZeroDimGB:=groebnerBasis(sub(Y+Ls+G+LA,R)+EqT, Strategy=>"F4");
        pd=numColumns basis(cokernel leadTerm ZeroDimGB);
    );
    return pd;
);

eXYmult=method(TypicalValue=>ZZ,Options => {HomMethod=>2,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4,Verbose=>false});
eXYmult (Ideal,Ideal) := opts->(I1,I2) -> (
    if opts.Verbose then print "eXYmult(I,J) computes e_XY where X is the top equidimensional component of V(I) and Y=V(J) (Y is assumed to be irreducible)";
    Iinfo:=new MutableHashTable;
    A:=ChowRing(ring(I2));
    Iinfo#"A"=A;
    clX:=chowClass(I1+I2,Iinfo,CompMethod=>"multidegree");
    seg:= Segre(I1,I2,A,HomMethod=>opts.HomMethod,ProjDegMethod=>opts.ProjDegMethod,SloppinessLevel=>opts.SloppinessLevel,Sparsity=>opts.Sparsity);
    mons:=flatten entries monomials clX;
    segMons:=sum(for m in mons list m*seg_(m));
    if opts.Verbose then <<"[X]= "<<clX<<" these monomials in Segre class= "<<segMons<<endl;
    return lift(segMons//clX,ZZ);
);

chowClass=method(TypicalValue=>ZZ,Options => {CompMethod=>"multidegree"});
chowClass Scheme := X -> (
    if X.chowClass==null then X.chowClass == chowClass(X.ideal);
    return (X.chowClass)
)
chowClass (Ideal) := opts -> (I) -> (
    R:=ring(I);
    A:=ChowRing(R);
    if opts.CompMethod=="multidegree" then (
        md:=multidegree (I);
        return sub(md,matrix{gens(A)});
    );
    -- Iinfo:=new MutableHashTable;
    -- Iinfo#"A"=A;
    -- degs:=unique degrees R;
    -- B:=flatten entries sort basis A;
    -- n:=numgens(R)-length(degs);
    -- tempId:={};
    -- PDl:={};
    -- for d in degs do (
    --     tempId={};
    --     for y in gens(R) do (
    --         if degree(y)==d then (
    --             tempId=append(tempId,y);
    --         );
    --     );
    --     PDl=append(PDl,ideal(tempId));
    -- );
    -- zdim:=0;
    -- for b in B do (
    --     if sum(flatten(exponents(b)))==n then zdim=b;
    -- );
    -- gbY := groebnerBasis(I, Strategy=>"MGB");
    -- codimY:= codim ideal leadTerm gbY;
    -- Iinfo#"PDl"=PDl;
    -- Iinfo#"B"=B;
    -- Iinfo#"zdim"=zdim;
    -- Iinfo#"gbY"=gbY;
    -- Iinfo#"codimY"=codimY;
    -- Iinfo#"m"=length degs;
    -- return chowClass(I,Iinfo,CompMethod=>opts.CompMethod);
);
chowClass (Ideal,MutableHashTable):=opts->(I,Info)->(
    R:=ring I;
    A:=Info#"A";
    classI:=0;
    if opts.CompMethod=="multidegree" then (
        md:=multidegree (I);
        classI=sub(md,matrix{gens(A)});
    ) else (
    PDl:=Info#"PDl";
    B:=Info#"B";
    c:={};
    ZeroDimGB:=0;
    ve:=0;
    Ls:=0;
    v:=0;
    LA:=0;
    gbY:=Info#"gbY";
    m:=Info#"m";
    codimY:=Info#"codimY";
    zdim:=Info#"zdim";
    kk:=coefficientRing(R);
    for p in PDl do (
        LA=LA+ideal(1-sum(numgens(p),i->random(kk)*p_i));
    );
    for w in B do if sum(flatten(exponents(w)))==codimY then c=append(c,w);
        for w in c do (
            Ls=0;
            v=zdim//w;
            ve=flatten exponents(v);
            for i from 0 to length(ve)-1 do (
                if ve_i!=0 then (
                    Ls=Ls+sum(ve_i,j->ideal(random(OneAti(m,i),R)));
                );
            );
            ZeroDimGB=ideal groebnerBasis(ideal(gbY)+Ls+LA, Strategy=>"F4");
            classI=classI+(numColumns basis(cokernel leadTerm ZeroDimGB))*w;
        );
    );
    return classI;
);

isMultiHomogeneous=method(TypicalValue=>Boolean);
isMultiHomogeneous Ideal:=I->(
    Igens:=flatten entries gens(I);
    d:=0;
    fmons:=0;
    for f in Igens do (
        fmons=flatten entries monomials(f);
        if length(fmons)>1 then (
            d=degree(first(fmons));
            for mon in fmons do (
                if degree(mon)!=d then (
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

makeMultiHom=method(TypicalValue=>Ideal);
--TODO Replace this (Ideal,Ideal,ZZ) version with a wrapper for the Hash input version below
makeMultiHom (Ideal,Ideal,ZZ):=(K,J,dimY)->(
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
    pdlHashList:={};
    for d in degs do (
        tempId={};
        for y in gens(R) do (
            if degree(y)==d then (
                tempId=append(tempId,y);
            );
        );
        pdlHashList=append(pdlHashList,{d,tempId});
        PDl=append(PDl,tempId);
    );
    irelHash:=hashTable(pdlHashList);
    for f in gensI do (
        if degree(f)==maxDegs then (
            homGens=append(homGens,f);
        ) else (
            degDif=maxDegs-degree(f);
            tempfGens=ideal(f);
            for i from 0 to #degDif-1 do (
                curIrel=irelHash#(OneAti(deglenR,i));
                tempfGens=tempfGens*ideal(for g in curIrel list g^(degDif_i));
            );
        homGens=join(homGens,flatten entries gens tempfGens);
        );
    );
    return ideal for j from 0 to dimY list sum(homGens,l->l*random(kk)*random(0,4));
    --return ideal homGens;
);
makeMultiHom (Ideal,Ideal,MutableHashTable):=(K,J,InfoHash)->(
    I:=K+J;
    R:=ring I;
    deglenR:=degreeLength R;
    degs:=unique degrees R;
    n:=InfoHash#"n";
    kk:=coefficientRing R;
    gensI:= delete(0_R,flatten sort entries gens K);
    homGens:={};
    degI:= degrees I;
    maxDegs:=InfoHash#"maxDegs";
    curIrel:=0;
    degDif:=0;
    tempfGens:=0;
    irelHash:=InfoHash#"irelHash";
    for f in gensI do (
        if degree(f)==maxDegs then (
            homGens=append(homGens,f);
        ) else (
            degDif=maxDegs-degree(f);
            tempfGens=ideal(f);
            for i from 0 to #degDif-1 do (
                curIrel=irelHash#(OneAti(deglenR,i));
                tempfGens=tempfGens*ideal(for g in curIrel list g^(degDif_i));
            );
            homGens=join(homGens,flatten entries gens tempfGens);
        );
    );
    return ideal for j from 0 to InfoHash#"dimY" list sum(homGens,l->l*random(kk)*random(0,4));
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
    if not isField(kk) then (
        <<"The coefficent ring must be a field, using the default field kk=ZZ/32749"<<endl;
        kk=ZZ/32749;
    );
    m:=length(l);
    numVars:=sum(l)+m;
    degs:={};
    ind:=0;
    for n in l do (
        for i from 0 to n do (
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
    -- Rgens:=gens R;
    Rdegs:=degrees R;
    -- degd:=0;
    -- eqs:=0;
    ChDegs:=unique Rdegs;
    m:=length ChDegs;
    C:=ZZ[h_1..h_m,Degrees=>ChDegs];
    K:={};
    -- inds:={};
    -- rg:=0;
    ns:={};
    temp:=0;
    for d in ChDegs do (
        temp=0;
        for a in Rdegs do (
            if d==a then temp=temp+1;
        );
        ns=append(ns,temp);
    );

    for i from 0 to length(ChDegs)-1 do (
        K=append(K,C_(i)^(ns_i));
    );
    K=substitute(ideal K,C);
    A:=C/K;
    return A;
);

Segre=method(TypicalValue => RingElement,Options => {HomMethod=>2,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4,Verbose=>false});
Segre (Ideal,Ideal) :=opts-> (I1,I2) -> (
    --print "start segre wrapper";
    A:=ChowRing(ring(I2));
    return Segre(I1,I2,A,opts);
);
Segre (Ideal,Ideal,QuotientRing) :=opts->(X,Y,A) -> (
    --------------------------------------------------------
    -------Initilization Begins-----------------------------------
    if not isMultiHomogeneous(X) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHomogeneous(Y) then (print "the second ideal is not multi-homogenous, please correct this"; return 0;);
    Rx:=ring X;
    Ry:=ring Y;
    kk:=coefficientRing Ry;
    if opts.ProjDegMethod=="NAG" and char(kk)!=0 then (print "Use QQ for NAG"; return 0;);
    B:=flatten entries sort basis A;
    -- degs:=unique degrees Ry;
    tempId:={};
    PDl:={};
    pdlHashList:={};
    for d in unique degrees Ry do (
        tempId={};
        for y in gens(Ry) do (
            if degree(y)==d then (
                tempId=append(tempId,y);
            );
        );
        PDl=append(PDl,ideal(tempId));
        pdlHashList=append(pdlHashList,{d,tempId});
    );
    irelHash:=hashTable(pdlHashList);
    --this saturation might or might not be a good idea
    X=saturate(X,product(PDl));
    Y=saturate(Y,product(PDl));
    n:=numgens(Ry)-length unique degrees Ry;
    --find the max multidegree, write it as a class alpha
    degX:= degrees (X+Y);
    transDegX:= transpose degX;
    maxDegs:= for i from 0 to length(transDegX)-1 list max transDegX_i;
    deg1B:={};
    for w in B do if sum(degree(w))==1 then deg1B=append(deg1B,w);
    m:=length unique degrees Ry;
    alpha:=sum(length deg1B,i->(basis(OneAti(m,i),A))_0_0*maxDegs_i);
    zdim:=0;
    for b in B do (
        if sum(flatten(exponents(b)))==n then zdim=b;
    );
    seg:=0;
    --find gb's
    gbX := groebnerBasis(X+Y, Strategy=>"MGB");
    gbY := groebnerBasis(Y, Strategy=>"MGB");
    codimX := codim ideal leadTerm gbX;
    codimY:= codim ideal leadTerm gbY;
    dimX := n-codimX;
    dimY:= n-codimY;
    c:={};
    v:=0;
    Ls:=0;
    ve:=0;
    ZeroDimGB:=0;
    LA:=0;
    --clY:=0;
    -------------------------------
    --common info that will be needed by functions (both existing funcs and TODO funcs)
    --could be switched to an object
    ShareInfo:=new MutableHashTable;
    ShareInfo#"R"=Ry;
    ShareInfo#"A"=A;
    ShareInfo#"B"=B;
    ShareInfo#"n"=n;
    ShareInfo#"m"=m;
    ShareInfo#"dimY"=dimY;
    ShareInfo#"codimY"=codimY;
    ShareInfo#"gbY"=gbY;
    --the computation of these (above) could be moved to a function
    ShareInfo#"irelHash"=irelHash;
    ShareInfo#"PDl"=PDl;
    ShareInfo#"maxDegs"=maxDegs;
    ShareInfo#"zdim"=zdim;
    -------------------------------
    clY:=chowClass(Y,ShareInfo,CompMethod=>"prob");
    if opts.Verbose then <<"[Y]= "<<clY<<", alpha= "<<alpha<<endl;
    W:=X+Y;
    Wg:=0;
    G:=0;
    pd:=0;
    EqT:=0;
    c={};
    projectiveDegreesList := {};
    deltaDegreesList := {};
    --------------------------------------------------------
    -------Initilization Ends-----------------------------------
    -----Begin Main Process------------------------------
    for i from 0 to dimX do (
        for w in B do (
            if sum(flatten exponents(w))==n-i then (
                pd=projectiveDegree(X, Y,{w,i},ShareInfo,opts);
                projectiveDegreesList = append(projectiveDegreesList,pd*w);
            );
        );
    );
    if opts.Verbose then <<"Projective degrees= "<<projectiveDegreesList<<endl;
    --build Segre class recursivly from Proj Degs
    Gam:=sum(projectiveDegreesList);
    SegClass:=0_A;
    temp7:=0;
    temp9:=0;
    RHS:=sum(0..dimX,i->alpha^(dimY-i)*clY)-Gam;
    for i from 0 to dimX do (
        for w in B do (
            if sum(flatten exponents(w))==n-(dimX-i) then (
                temp9=(zdim//w);
                temp7=RHS_(w)-(temp9*(1+alpha)^(dimY-sum(flatten exponents(temp9)))*SegClass)_(zdim);
                SegClass=SegClass+temp7*w;
                --<<"w= "<<w<<", SegClass= "<<SegClass<<" coeff= "<<(1+alpha)^(dimY-sum(flatten(exponents(temp9))))<<endl;
            );
        );
    );
    if opts.Verbose then <<"s(X,Y)= "<<SegClass<<endl;
    -- use Ry;
    return SegClass;
);


----------------------------
-- utility functions
----------------------------


OneAti=(dl,i)->(
    vec:={};
    for j from 0 to dl-1 do (
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
    for a in bloks do (
        elList={};
        for r in Rgens do (
            if degree(r)==a then (
                elList=append(elList,r);
            );
        );
        irId=irId*ideal(elList)
    );
    return irId;
)


TEST ///
-- union of coordinate axes in PP3 (diagonal)
{*
restart
needsPackage "EffIntThy"
*}
R = MultiProjCoordRing({3,3})
x = gens(R)
D = minors(2,matrix{{x_0..x_3},{x_4..x_7}})
X = ideal(x_0*x_1,x_1*x_2,x_0*x_2)
A = ZZ[a,b,Degrees=>{{1,0},{0,1}}]/(a^4,b^4)
s = Segre(X,D,A)
assert(s == 3*(a^3*b^2+a^2*b^3)-10*(a^3*b^3))
///

TEST ///
{*
restart
needsPackage "EffIntThy"
*}
R=MultiProjCoordRing({6})
x=gens(R)
degrees R
I=ideal(random(2,R),x_0^4-x_1*x_3^3-x_4*x_5^3)
J=ideal(x_0*x_2-x_4*x_5)
chowClass(J,CompMethod=>"prob")
A = ZZ[h]/(h^7)
assert(Segre(I,J,A)==16*h^3-96*h^4+448*h^5-1920*h^6)
assert(eXYmult(I,J)==1)
///

end

restart
needsPackage "EffIntThy"
R = ZZ/32003[x,y,z,w];
I = ideal(-z^2+y*w,-y*z+x*w)
J = ideal(-z^3+2*y*z*w-x*w^2,-y^2+x*z)
time mult=eXYmult(I,J)
mult==2

restart
needsPackage "EffIntThy"
kk=ZZ/32749
R = MultiProjCoordRing(kk,{2,3})
x=(gens R)_{0..2}
y=(gens R)_{3..6}
I=ideal(x_0^2*x_1*y_1^2-x_0^3*y_0*y_3)
J=ideal(x_1^2*x_0*y_3^2-x_0^3*y_2*y_0-x_0^3*y_0^2)
time seg=Segre(I,J)

restart
needsPackage "EffIntThy"
R=MultiProjCoordRing({3,3})
x=(gens(R))_{0..3}
y=(gens(R))_{4..7}
--Qx=random({2,0},R)
Qx = ideal (x#0*x#1 - x#2*x#3)
Qy=sub(Qx,matrix{join(y,for i from 4 to 7 list 0)})
D = minors(2,matrix{x,y})
I=ideal(Qx,Qy,D) --QxQ in the diagional
Cx=ideal random({1,0},R)
s=Segre(Cx,I)

restart
needsPackage "EffIntThy"
R=MultiProjCoordRing({2,1});
x=(gens R)_{0..2};
y=(gens R)_{3..4};
-- I=ideal(random({1,0},R),random({1,0},R)) --a point in P^2
I = ideal (x_0,x_1);  -- choosing a simple point to make things easier
B=ideal(y_0*I_1-y_1*I_0); ---blow up of this point...
E=B+ideal (x_0,x_1);
s=Segre(E,B)

restart
needsPackage "EffIntThy"
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
