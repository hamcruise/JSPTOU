int nj = ...;
int nm = ...;
range Jobs = 1..nj;
range Mchs = 1..nm;
int pidle[m in Mchs] = ...;
tuple t_Op {
  int j;   
  int pos; 
  int m;  
  int pt;
  int end; 
  int prevMch;
  int po; //encery consumption Uniform[3,5]
            
};
{t_Op} Ops=...;
execute  { cplex.tilim = 10; cplex.epagap=1e-08;}
int bigM= sum (o in Ops) o.pt;

//############## Dynamic Energy Price Related ##############
int P = 5;// common power
int days=ftoi(round(bigM/24))+1; 

range hrs0=0..24*days-1;//Times
int T=days*24;  
int p[1..24]=[26,26,27,26,26,29,36,46,44,39,53,47,42,42,40,39,48,67,78,80,81,73,63,48];
int ep[1..T];
execute {
for(var h=1;h<=24;h++)
	for(var d=0;d<=days-1;d++)
		ep[d*24+h]=p[h];	
}
//############## Dynamic Energy Price Related for Speedy Computation##############
tuple tcumEStartingAtT {
  key int j; //id 
  key int pos; //pos 
  key int m;
  key int t;
  int e; // sum of energy price when oper id on machine m starts at time t  
} {tcumEStartingAtT} cumEStartingAtT;
int t0Price[Ops];

execute {
var sumPrice=0;
for(var o in Ops) 
	for(var t in hrs0) if(t<=24*days-o.pt-1) {
		for(var h=t; h<=t+o.pt-1; h++) sumPrice+=ep[h+1];
   	   	 cumEStartingAtT.add(o.j,o.pos,o.m,t,sumPrice);
   	   	   	if(t==0) t0Price[o]=sumPrice;
   	   	   	sumPrice=0;	
        }        	   	   		
}
pwlFunction CumPrice[o in Ops] = 
	piecewise(c1,c2 in cumEStartingAtT: c1!=c2 && c1.pos==c2.pos && c1.j==c2.j && c1.m==c2.m && c1.t+1 ==c2.t && o.m==c1.m && o.j==c1.j  && o.pos==c1.pos) 
	{ c2.e - c1.e -> c1.t+1; 0}(0, t0Price[o]);

tuple tcumEndingAtT {
  int t;
  int e; // sum of energy price when oper id on machine m starts at time t  
} {tcumEndingAtT} cumEndingAtT;
execute {
var sumPrice=ep[1];
for(var t=0; t<=T-1; t++) {
  	 cumEndingAtT.add(t,sumPrice);
  	 if(t>=1) sumPrice+= ep[t+1];
  	 else     sumPrice+= 0;
 }        	   	   		
}
pwlFunction CumIdle = 
	piecewise(c1,c2 in cumEndingAtT: c1.t+1 ==c2.t)
	{ c2.e - c1.e -> c1.t+1; 0}(0, ep[1]);

dvar int+ X[Ops];
dvar boolean Z[Ops][Ops][Mchs];
dvar float+ cmax;
dexpr float energy_common=CumIdle(cmax)*P;
dexpr float energy_prod=sum(o in Ops) CumPrice[o](X[o]) *o.po;
dexpr float energy_idle=sum(m in Mchs) CumIdle(cmax)*pidle[m]
 					  - sum(o in Ops) CumPrice[o](X[o]) *pidle[o.m];
dexpr float energy_total=energy_common+energy_prod + energy_idle;

minimize energy_total;
subject to {
  forall (o1, o2 in Ops: o1.j==o2.j && o1.pos+1==o2.pos) 
      X[o1] + o1.pt <= X[o2];
  forall (o1, o2 in Ops: o1!=o2 && o1.m==o2.m) 
      X[o1] >= X[o2] + o2.pt - bigM*Z[o1][o2][o1.m];
  forall (o1, o2 in Ops: o1!=o2 && o1.m==o2.m) 
      X[o2] >= X[o1] + o1.pt - bigM*(1-Z[o1][o2][o1.m]);
  forall (o in Ops: o.end==1)
    cmax >= X[o] + o.pt;       
}

execute {
writeln("makespan        = ", cmax);
writeln("energy_common   = ", energy_common);
writeln("energy_prod     = ", energy_prod);
writeln("energy_idle     = ", energy_idle);
writeln("energy_total    = ", energy_total);
};

