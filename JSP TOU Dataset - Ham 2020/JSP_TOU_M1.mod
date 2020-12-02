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

int bigM= sum (o in Ops) o.pt;

//############## Dynamic Energy Price Related ##############
int P = 5;// common power
int days=ftoi(round(bigM/24))+1; //85; //75;

range hrs0=0..24*days-1;//Times
range hrs1=0..24*days-2; //Times1

int T=days*24;  
int p[1..24]=[26,26,27,26,26,29,36,46,44,39,53,47,42,42,40,39,48,67,78,80,81,73,63,48];
int ep[1..T];
execute {
for(var h=1;h<=24;h++)
	for(var d=0;d<=days-1;d++)
		ep[d*24+h]=p[h];	
}
execute  { cplex.tilim = 60; cplex.epagap=1e-08;
}

dvar boolean W[Ops][hrs0];
dvar boolean L[hrs0];
dvar float+ cmax;
dexpr float energy_common=sum(t in hrs0) P*ep[t+1]*L[t];
dexpr float energy_prod=sum(o in Ops, r,t in hrs0: r >=t && r <= t+o.pt-1) o.po*ep[r+1]*W[o][t];
dexpr float energy_idle=sum(m in Mchs, t in hrs0) pidle[m]*ep[t+1]*L[t]
                       -sum(o in Ops, r,t in hrs0: r >=t && r <= t+o.pt-1) pidle[o.m]*ep[r+1]*W[o][t];
dexpr float energy_total=energy_common+energy_prod + energy_idle;

minimize energy_total;
subject to {
  forall (o in Ops) sum(t in hrs0: t <= T-o.pt) W[o][t] == 1;

  forall (o1, o2 in Ops: o1.j==o2.j && o1.pos+1==o2.pos) 
      sum(t in hrs0: t <= T-o1.pt) W[o1][t]*(t+o1.pt) <=
      sum(t in hrs0: t <= T-o2.pt) W[o2][t]*t;
  forall (m in Mchs, t in hrs0) 
  	  sum(o in Ops, r in hrs0: o.m==m && r>=t-o.pt+1 && r <=t) W[o][r] <= 1;
  forall (t in hrs1) L[t] >= L[t+1];    
  forall (o in Ops, r,t in hrs0: r==t+o.pt-1) L[r] >= W[o][t];
  forall (o in Ops, t in hrs0) L[t] >= W[o][t] ;
  cmax == sum(t in hrs0) L[t];   
    
}
execute {
writeln("makespan        = ", cmax);
writeln("energy_common   = ", energy_common);
writeln("energy_prod     = ", energy_prod);
writeln("energy_idle     = ", energy_idle);
writeln("energy_total    = ", energy_total);

writeln("m"+"\t"+"j"+"\t"+"o"+"\t"+"pw"+"\t" +"pt"+"\t" +"s"+"\t"+"e");
  for(var o in Ops) for(var t in hrs0)
    if (W[o][t] == 1)
	  writeln(o.m+"\t"+o.j+"\t"+o.pos+"\t"+o.po+"\t"+o.pt+"\t"+t+"\t"+(t+o.pt));
}
