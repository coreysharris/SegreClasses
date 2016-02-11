newPackage(
     	"SegreAlpha1",
	Version =>"0.1",
    	Date => "Jan 13, 2016",
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
   "Segre",
   "ChowRing"

}

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
Segre=method(TypicalValue => RingElement); 
Segre (Ideal,Ideal) := (I1,I2) -> ( 
    A:=ChowRing(ring(I2));
    return Segre(I1,I2,A);
    );
--Compute s(X,Y)=s(V(I1),V(I2))   
Segre (Ideal,Ideal,QuotientRing) := (I1,I2,A) -> ( 
    R11:=ring(I1);
    R22:=ring(I2);
    --this check really isn't quite adequate, fix later
    if (not (gens(R11)==gens(R22))) then(
	error "Rings don't match";
	);
    --Find dimension of Y
    R:=ring I2;
    kk:=coefficientRing R;
    n:=numgens(R) -1;
    gbI2 := groebnerBasis(I2, Strategy=>"MGB");
    N := n-codim ideal leadTerm gbI2;
    --Degree only depends on the leading monomials of a GB, also degree will not change 
    --when Y is cut with hyperplanes
    degY:=degree monomialIdeal gbI2;
    --Find dimension of X
    gbI1 := groebnerBasis(I1, Strategy=>"MGB");
    dimX := n-codim ideal leadTerm gbI1;
    --take care of empty X and Y=P^n
    if (dimX<0) or (N<0) then return 0;
    if ideal(gbI2)==ideal(1_R) then return Segre(I1);
    
    --Make new affine ring to count points
    t:=symbol t;
    R3:=kk[gens R,t];
    K1:=substitute(I1,R3) ;
    
    --initialize variables
    delta:={}; 
    d:=first max degrees I1;
    dl:={d};
    m:=numgens I1;
    hypers:=0;
    EqT:=0;
    Wt:=0;
    tall:=0;
    Rgens := (gens R3)_{0..n};
    gbWt2:=0;
    segre:=0;
    segreList:={};
    LA:=0;
    temp:=0;
    --get Chow ring generator (only for P^n at the moment)
    h:=A_0;

    --Make Linear Forms and combinations of gens X_i
    L:=for i from 1 to N list sum(numgens R,j->random(kk)*Rgens_j);
    F:={};
    --Make all generators of X have the same degree in the loop
    for i from 1 to N do(
	F=append(F,sum(i,j->ideal(sum(flatten entries gens(K1),g->g*random(kk)*substitute(random(dl-degree(g),R),R3))+sum(N-i,l->random(kk)*L_l) )));
	);
    --Deal with k=0 case
    LA=ideal(1-sum(numgens R,j->random(kk)*Rgens_j));
    EqT=ideal( sum((numgens I1),i->(1-t*random(kk)*substitute(I1_i,R3))));
    Wt=F_(N-1)+EqT+substitute(ideal(gbI2),R3)+LA; 
    gbWt2 = groebnerBasis(Wt, Strategy=>"F4");
    tall=numColumns basis(cokernel leadTerm gbWt2);
    delta = append(delta,d^N*degY-tall);
    --<<"tall= "<<tall<<endl;
    for k from 1 to dimX do (
	--need k hyperplanes to intersect Y with
	hypers=ideal take(L,k);
	LA=ideal(1-sum(numgens R,j->random(kk)*Rgens_j));
	--remove X
	EqT=ideal( sum((numgens I1),i->(1-t*random(kk)*substitute(I1_i,R3))));
	--Pick a F with N-k linear combos of the gens of X_i=(X cut with i=k hyperplanes) 
	Wt=substitute(ideal(gbI2),R3)+hypers+F_(N-1-k)+EqT+LA;
	gbWt2 = groebnerBasis(Wt, Strategy=>"F4");
	tall = numColumns basis(cokernel leadTerm gbWt2);
	delta=append(delta,d^(N-k)*degY-tall);
	--<<"tall= "<<tall<<endl;
	);
    --this part is probabally not needed...
    --for k from dimX+1 to N do(
    --	delta=append(delta,d^(N-k)*degY); 
    --	);
    <<"delta= "<<delta<<endl;
    --build Segre class
    for i from 0 to dimX do(
	--temp=for j from 0 to i-1 list binomial(N-dimX+i,j+1)*d^(j+1);
	--print temp;
	--print delta_(dimX-i);
	segreList=prepend(delta_(dimX-i)-(sum(i,j->binomial(N-dimX+i,j+1)*d^(j+1)*segreList_(i-j-1)) ),segreList);
	); 
    
    segre=sum(length(segreList),i->segreList_i*h^(n-i));
    use R;
    return segre;
    );
Segre (Ideal) := (I) -> ( 
    A:=ChowRing(ring(I));
    return Segre(I,A);
    );
--Compute s(X,P^n)=s(V(I),P^n) 

Segre (Ideal, QuotientRing):=(I,A)->( 
    --Find dimension of X
    R:=ring I;
    kk:=coefficientRing R;
    n:=numgens(R) -1;
    gbI := groebnerBasis(I, Strategy=>"MGB");
    codimX := codim ideal leadTerm gbI;
    degX:=degree monomialIdeal gbI;
    
    --Make new affine ring to count points
    t:=symbol t;
    R3:=kk[gens R,t];
    K1:=substitute(I,R3) ;
    
    --initialize variables
    d:=first max degrees I;
    dl:={d};
    m:=numgens I;
    hypers:=0;
    EqT:=0;
    Wt:=0;
    tall:=0;
    Rgens := (gens R3)_{0..n};
    gbWt2:=0;
    LA:=0;
    gensI:=flatten entries gens I;
    J:= for i from 1 to n list sum(gensI,g -> g*random(kk)*random({d}-degree(g),R));
    
    --get Chow ring generator
    h:=A_0;
    --Calculate Projective Degrees
    g:=for i from 0 to codimX-1 list d^i;
    g=append(g,d^(codimX)-degX);
    for i from codimX+1 to n do(
	LA=ideal(1-sum(numgens R,j->random(kk)*Rgens_j));
	EqT=ideal( sum((numgens I),i->(1-t*random(kk)*substitute(I_i,R3))));
	hypers=sum(n-i,l->ideal(sum(numgens R,j->random(kk)*Rgens_j)));
	Wt=substitute(ideal(take(J,i)),R3)+hypers+EqT+LA;
	gbWt2 = groebnerBasis(Wt, Strategy=>"F4");
	tall = numColumns basis(cokernel leadTerm gbWt2);
	g=append(g,tall);
	);
    G:=sum(0..n,s->g_s*h^s*(1+d*h)^(n-s));
    segre:=1 - G* sum(0..n,i->binomial(n+i,i)*(-d*h)^i);
    return segre;
    );

TEST ///
{*  
    restart
    needsPackage "SegreAlpha1"
*} 
    kk=ZZ/32749;
    R=kk[x_0..x_3];
    A=ChowRing(R)
    
    C = ideal(x_0^3-x_0*x_1^2-x_0*x_2^2+2*x_1*x_2*x_3-x_0*x_3^2)
    J = ideal mingens ideal singularLocus C
    Segre(J,C)  
    Segre(J,C,A)   
    Segre C
    Segre(C,A)
    
///
TEST ///
{*  
    restart
    needsPackage "SegreAlpha1"
*} 
    kk=ZZ/32749;
    R=kk[x_0..x_3];
    X = ideal(x_0,x_1)
    Y=ideal(x_0*x_1+x_2^2)
    Segre(X+Y,Y)
    Segre X
    
///

TEST ///
{*  
    --Segre P^1xP^2 -> P^5
    restart
    needsPackage "SegreAlpha1"
*} 
    kk=ZZ/32749;
    R=kk[x_0..x_4];
    X = ideal(x_0^2-x_1*x_2,x_3+5*x_4)
    Y=ideal(x_0*x_3-x_1^2+4*x_2*x_3)
    Segre(X+Y,Y)
    codim(X+Y)
    
///