using CP;
int nj = ...;
int nm = ...;
range Mchs = 1..nm;
int pidle[m in Mchs] = ...;
tuple t_Op {
  int j;   
  int pos; 
  int m;  
  int pt;
  int end; 
  int prevMch;
  int e; //encery consumption Uniform[3,5]
            
};
{t_Op} Ops=...;


int bigM= sum (o in Ops) o.pt;

//############## Dynamic Energy Price Related ##############
int P = 5;// common power
int days=ftoi(round(bigM/24))+1; //85; //75;
range hrs0=0..24*days-1;
range hrs=1..24*days-1;
int horizon=days*24;  
int p[1..24]=[26,26,27,26,26,29,36,46,44,39,53,47,42,42,40,39,48,67,78,80,81,73,63,48];
int ep[1..horizon];
execute {
for(var h=1;h<=24;h++)
	for(var d=0;d<=days-1;d++)
		ep[d*24+h]=p[h];	
}
stepFunction EnergyPrice = stepwise(h in hrs) { ep[h]-> h*100; ep[1]}; 
dvar interval eMakespan in 0..horizon*100 intensity EnergyPrice;

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
//writeln(t0Price);
//writeln(cumEStartingAtT);
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
for(var t=0; t<=horizon-1; t++) {
  	 cumEndingAtT.add(t,sumPrice);
  	 if(t>=1) sumPrice+= ep[t+1];
  	 else     sumPrice+= 0;
 }        	   	   		
}
pwlFunction CumIdle = 
	piecewise(c1,c2 in cumEndingAtT: c1.t+1 ==c2.t)
	{ c2.e - c1.e -> c1.t+1; 0}(0, ep[1]);

dvar interval itvs[o in Ops] in 0..horizon size o.pt ;
dvar interval makespan in 0..horizon;
dvar sequence seqMchs[m in Mchs] in all(o in Ops : o.m == m) itvs[o];
		  
dexpr int cmax=  max(o in Ops: o.end==1) endOf(itvs[o]);
dexpr float energy_common=endEval(makespan, CumIdle)*P;
dexpr float energy_prod=sum(o in Ops) startEval(itvs[o], CumPrice[o])*o.e;
dexpr float energy_idle=sum(m in Mchs) endEval(makespan, CumIdle)*pidle[m]
 					  - sum(o in Ops) startEval(itvs[o], CumPrice[o])*pidle[o.m];;
dexpr float energy_total=energy_common + energy_prod + energy_idle;

execute {
  cp.param.TimeLimit = 5;
  cp.param.LogVerbosity=21;  
  cp.param.NoOverlapInferenceLevel = "Extended"  
  cp.param.RelativeOptimalityTolerance=1e-08;
} 			  	
minimize energy_total;
subject to {
  startOf(makespan)==0;
  endOf(makespan)==cmax;
  forall (m in Mchs)
    noOverlap(seqMchs[m]);
  forall (o1, o2 in Ops:o1.j==o2.j && o1.pos+1==o2.pos)
    endBeforeStart(itvs[o1], itvs[o2]);
}

execute {
writeln("makespan        = ", cmax);
writeln("energy_common   = ", energy_common);
writeln("energy_prod     = ", energy_prod);
writeln("energy_idle     = ", energy_idle);
writeln("energy_total    = ", energy_total);
writeln("m"+"\t"+"j"+"\t"+"o" +"\t"+ "pw" +"\t"+ "pt"+"\t"+ "s"+"\t"+ "e");
for(var o in Ops) 
    writeln(o.m + "\t" + o.j +"\t"+ o.pos +"\t"+ o.e +"\t" + o.pt  
    +"\t"+ itvs[o].start  +"\t"+ itvs[o].end);
}