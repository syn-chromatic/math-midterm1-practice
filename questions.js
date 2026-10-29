/* Math Midterm 1 Practice: the 8 task types from the sample exam sheet, with new numbers every time.
   Loads after engine.js. The first load shows the exact numbers from the sample sheet.
   On the exam, tasks 1, 3, 4 and 6 share one matrix A; "Practise all with new numbers" keeps that. */
(function(){
"use strict";
const {pick,mi,up,sb,OP,FR,EQ,CALC,IMPLIES,legend,steps,checkline,finalAns,watch}=HL;

/* ---------- random numbers ---------- */
const R=n=>Math.floor(Math.random()*n);
const ri=(a,b)=>a+R(b-a+1);
const rnz=(a,b)=>{let x;do{x=ri(a,b);}while(x===0);return x;};
const shuffle=a=>{a=a.slice();for(let i=a.length-1;i>0;i--){const j=R(i+1);[a[i],a[j]]=[a[j],a[i]];}return a;};

/* ---------- exact arithmetic and number display ---------- */
const gcd=(a,b)=>{a=Math.abs(a);b=Math.abs(b);while(b){const t=a%b;a=b;b=t;}return a||1;};
const red=(n,d)=>{if(d<0){n=-n;d=-d;}const g=gcd(n,d);return [n/g,d/g];};
const r3=x=>{const v=Math.round(x*1000)/1000;return Object.is(v,-0)?0:v;};
const nm=v=>{if(typeof v!=="number")return v;v=r3(v);return v<0?`−${-v}`:`${v}`;};
const pn=v=>typeof v==="number"&&r3(v)<0?`(${nm(v)})`:nm(v);
const frH=(n,d)=>{const [a,b]=red(n,d);return b===1?nm(a):`${a<0?"−":""}${FR(Math.abs(a),b)}`;};
const approx=(n,d)=>{const [a,b]=red(n,d);return b===1?"":` ≈ ${nm(a/b)}`;};
const sum=a=>a.reduce((s,v)=>s+v,0);
const sumS=vals=>vals.map((v,i)=>i===0?nm(v):(r3(v)<0?` − ${nm(-v)}`:` + ${nm(v)}`)).join("");

/* ---------- matrices (whole numbers) ---------- */
const det2=m=>m[0][0]*m[1][1]-m[0][1]*m[1][0];
const minor=(m,i,j)=>m.filter((_,r)=>r!==i).map(row=>row.filter((_,k)=>k!==j));
const det=m=>m.length===1?m[0][0]:m.length===2?det2(m):m[0].reduce((s,v,j)=>s+(j%2?-1:1)*v*det(minor(m,0,j)),0);
const sgn=(i,j)=>(i+j)%2?-1:1;
const cofM=m=>m.map((r,i)=>r.map((_,j)=>sgn(i,j)*det(minor(m,i,j))));
const minM=m=>m.map((r,i)=>r.map((_,j)=>det(minor(m,i,j))));
const tr=m=>m[0].map((_,j)=>m.map(r=>r[j]));
const mul=(a,b)=>a.map(r=>b[0].map((_,j)=>r.reduce((s,v,k)=>s+v*b[k][j],0)));
const madd=(a,b)=>a.map((r,i)=>r.map((v,j)=>v+b[i][j]));
const msub=(a,b)=>a.map((r,i)=>r.map((v,j)=>v-b[i][j]));
const msum=m=>sum(m.flat());
const withCol=(m,j,col)=>m.map((r,i)=>r.map((v,k)=>k===j?col[i]:v));
const withRow=(m,i,row)=>m.map((r,k)=>k===i?row.slice():r.slice());
const adj2=m=>[[m[1][1],-m[0][1]],[-m[1][0],m[0][0]]];

/* ---------- typesetting ---------- */
const svg=(cls,d)=>`<svg class="br ${cls}" viewBox="0 0 10 100" preserveAspectRatio="none" aria-hidden="true"><path d="${d}"/></svg>`;
const BRK={
  p:[svg("br-l","M8.5 1.5C1.5 28 1.5 72 8.5 98.5"),svg("br-r","M1.5 1.5C8.5 28 8.5 72 1.5 98.5")],
  d:[svg("br-l","M5 0V100"),svg("br-r","M5 0V100")],
  b:[svg("br-l","M9 1C5.5 1 5 4 5 10V42C5 47 3.5 49.5 1 50C3.5 50.5 5 53 5 58V90C5 96 5.5 99 9 99"),""]
};
/* MX(m,{k:"p"|"d", s:small, cls:(i,j)=>class, cell:(i,j,v)=>html}) draws a matrix (p) or a determinant (d). */
function MX(m,o={}){
  const k=o.k||"p",n=m[0].length;
  const cells=m.map((row,i)=>row.map((v,j)=>{const cls=o.cls?(o.cls(i,j)||""):"";const t=o.cell?o.cell(i,j,v):nm(v);return `<span class="mc${cls?" "+cls:""}">${t}</span>`;}).join("")).join("");
  return `<span class="mx mx-${k}${o.s?" mx-s":""}">${BRK[k][0]}<span class="mx-g" style="grid-template-columns:repeat(${n},auto)">${cells}</span>${BRK[k][1]}</span>`;
}
const DT=(m,o={})=>MX(m,Object.assign({k:"d"},o));
/* A system of equations with a brace. eqs:[{c:[coefficients],r:right side}], vars:[html]. o.mark(i,j) gives a highlight key (j = -1 for the right side). */
function SYS(eqs,vars,G,o={}){
  const n=vars.length,cells=[];
  eqs.forEach((e,i)=>{
    e.c.forEach((c,j)=>{
      const key=o.mark?o.mark(i,j):null,w=t=>key&&G?G(key,t):t;
      if(c===0){cells.push(j>0?'<span class="mc"></span><span class="mc"></span>':'<span class="mc"></span>');return;}
      const a=Math.abs(c),body=`${a===1?"":a}${vars[j]}`;
      if(j===0)cells.push(`<span class="mc">${c<0?"−":""}${w(body)}</span>`);
      else cells.push(`<span class="mc op-c">${c<0?"−":"+"}</span><span class="mc">${w(body)}</span>`);
    });
    const rk=o.mark?o.mark(i,-1):null;
    cells.push(`<span class="mc op-c">=</span><span class="mc">${rk&&G?G(rk,nm(e.r)):nm(e.r)}</span>`);
  });
  return `<span class="mx mx-b">${BRK.b[0]}<span class="mx-g sys" style="grid-template-columns:repeat(${2*n+1},auto)">${cells.join("")}</span></span>`;
}
const A_=mi("A"),B_=mi("B"),C_=mi("C"),X_=mi("X");
const DET=x=>`<span class="mu">det</span>&nbsp;${x}`;
const INV=x=>`${x}<sup>−1</sup>`;
const en=(l,i,j)=>sb(mi(l),`${i}${j}`);
const Cf=(i,j)=>sb(mi("C"),`${i}${j}`), Mn=(i,j)=>sb(mi("M"),`${i}${j}`);
const Cij=sb(mi("C"),mi("ij")), Mij=sb(mi("M"),mi("ij"));
const DEL=v=>v?sb(up("Δ"),v):up("Δ");
const VX=[mi("x"),mi("y"),mi("z")], VN=["x","y","z"];
const X4=[1,2,3,4].map(i=>sb(mi("x"),i)), SUBN=["₁","₂","₃","₄"];
const cross=(r,c)=>(i,j)=>i===r&&j===c?"hl":(i===r||j===c)?"x":"";
const wk=(...h)=>`<div class="wk">${h.map(x=>x.startsWith("<div")?x:`<span class="wk-i">${x}</span>`).join("")}</div>`;
const lines=ls=>`<div class="lines">${ls.map(l=>`<p class="calc sm">${l}</p>`).join("")}</div>`;
const signGrid=(n,hl)=>`<span class="dmath">${MX([...Array(n)].map((_,i)=>[...Array(n)].map((_,j)=>sgn(i,j)>0?"+":"−")),{s:1,cls:i=>i===hl?"hb":""})}</span>`;
const symM=(l,n,m)=>[...Array(n)].map((_,i)=>[...Array(m||n)].map((_,j)=>en(l,i+1,j+1)));
const in2=s=>`${pn(s[0][0])}·${pn(s[1][1])} − ${pn(s[0][1])}·${pn(s[1][0])}`;
const m2Line=s=>`${pn(s[0][0])} × ${pn(s[1][1])} − ${pn(s[0][1])} × ${pn(s[1][0])} = ${nm(s[0][0]*s[1][1])} − ${pn(s[0][1]*s[1][0])} = ${nm(det2(s))}`;
/* a 3×3 determinant worked along its first row */
function det3Lines(m){
  const sub=[0,1,2].map(j=>minor(m,0,j)),v=sub.map(det2),terms=[m[0][0]*v[0],-m[0][1]*v[1],m[0][2]*v[2]];
  return {d:sum(terms),v,terms,
    l1:`${pn(m[0][0])} × (${in2(sub[0])}) − ${pn(m[0][1])} × (${in2(sub[1])}) + ${pn(m[0][2])} × (${in2(sub[2])})`,
    l2:`${pn(m[0][0])} × ${pn(v[0])} − ${pn(m[0][1])} × ${pn(v[1])} + ${pn(m[0][2])} × ${pn(v[2])}`,
    l3:sumS(terms)};
}
const det3Work=(lhs,m)=>{const w=det3Lines(m);return CALC(`${lhs} = ${w.l1}`)+CALC(`= ${w.l2}`)+CALC(`= ${w.l3} = <b>${nm(w.d)}</b>`);};
const prodLines=(L,Rm,P)=>P.flatMap((r,i)=>r.map((v,j)=>`row ${i+1} · column ${j+1}: ${L[i].map((x,k)=>`${pn(x)}×${pn(Rm[k][j])}`).join(" + ")} = ${nm(v)}`));
/* x = a + b·x3 + c·x4 written out, with fractions over d */
function linH(parts,d){let s="";parts.forEach(([n,v])=>{const [a,b]=red(n,d);if(a===0)return;
  const body=b===1&&Math.abs(a)===1&&v?v:`${b===1?Math.abs(a):FR(Math.abs(a),b)}${v||""}`;
  s+=!s?`${a<0?"−":""}${body}`:` ${a<0?"−":"+"} ${body}`;});return s||"0";}
function linT(k0,terms){let s=k0===0?"":nm(k0);terms.forEach(([k,v])=>{if(k===0)return;const body=`${Math.abs(k)===1?"":Math.abs(k)}${v}`;s+=!s?`${k<0?"−":""}${body}`:` ${k<0?"−":"+"} ${body}`;});return s||"0";}

/* ---------- the exam's answer table ---------- */
const clean=(list,ans,rel=0,abs=1e-9)=>{const seen=new Set();return list.filter(t=>{if(!t||!Number.isFinite(t[0])||Math.abs(t[0]-ans)<=Math.abs(ans)*rel+abs)return false;const k=r3(t[0]);if(seen.has(k))return false;seen.add(k);return true;});};
const pmCands=(ans,tr)=>[-ans].concat(tr.flatMap(t=>[t[0],-t[0]]));
/* Five options like the sample sheet. About one time in five the right answer is left out, so (6) NP is correct. */
function makeOpts(ans,cands,np=true){
  const key=v=>r3(v).toFixed(3),seen=new Set([key(ans)]),pool=[];
  const push=v=>{if(!Number.isFinite(v)||Math.abs(v)>99999)return;const k=key(v);if(seen.has(k))return;seen.add(k);pool.push(r3(v));};
  cands.forEach(push);
  for(let s=1;pool.length<5&&s<60;s++){push(ans+s);push(ans-s);}
  const isNP=np&&Math.random()<0.2;
  return shuffle(pool.slice(0,4).concat([isNP?pool[4]:r3(ans)]));
}
function OPTS(p,ans,done,hasNP=true){
  const k=p.opts.findIndex(v=>r3(v)===r3(ans)),n=p.opts.length,right=i=>done&&(i===k||(k<0&&i===n));
  const th=p.opts.map((_,i)=>`<th scope="col">(${i+1})</th>`).join("")+(hasNP?`<th scope="col">(${n+1})</th>`:"");
  const td=p.opts.map((v,i)=>`<td${right(i)?' class="is-right"':""}>${nm(v)}</td>`).join("")+(hasNP?`<td${right(n)?' class="is-right"':""}>NP</td>`:"");
  return `<div class="opts-wrap"><table class="opts" aria-label="Answer options"><thead><tr>${th}</tr></thead><tbody><tr>${td}</tr></tbody></table></div>`;
}
function optLine(p,ans){
  const k=p.opts.findIndex(v=>r3(v)===r3(ans)),n=p.opts.length;
  return k>=0?`Your answer ${nm(ans)} is option <b>(${k+1})</b> in the table.`
    :`${nm(ans)} is not one of options (1) to (${n}), so on the exam you'd pick <b>(${n+1}) NP</b>. Trust your working: on the sample sheet, tasks 2 and 5 are NP too.`;
}

/* ---------- hint ladder pieces ---------- */
const EXACT={tol:0,abs:1e-6,fmt:nm,closeMsg:"Close, but not quite. With whole numbers in the matrix this answer comes out exact, so check each multiplication and every minus sign."};
const DEC={tol:0.003,abs:0.0006,fmt:nm,closeMsg:"Very close! Give 3 decimal places like the exam does (for example −0.383), or type the exact fraction (like −102/266)."};
function gEntry(M,i,j,o={}){
  const l=o.l||"a",v=M[i-1][j-1],t=[];
  if(v<0)t.push([-v,"Keep the minus sign: this number is negative."]);
  if(i!==j&&M[j-1]&&M[j-1][i-1]!==undefined&&M[j-1][i-1]!==v)t.push([M[j-1][i-1],`That's row ${j}, column ${i}. The first small number is the row (counted from the top), the second is the column (counted from the left).`]);
  return {k:`${l}${i}${j}`,sym:en(l,i,j),name:`row ${i}, column ${j}${o.of?` of ${o.of}`:""}`,unit:"",val:v,why:o.why||"",look:o.look||`Go down to row ${i}, then along to column ${j}.`,gtraps:t};
}
const markCells=(keys,G,l)=>(i,j,v)=>keys.some(([a,b])=>a===i+1&&b===j+1)?G(`${l}${i+1}${j+1}`,nm(v)):nm(v);
const TERMS={
  mx:["Matrix","A grid of numbers inside brackets. Rows go across, columns go down. A 3×3 matrix has 3 rows and 3 columns."],
  det:["Determinant","One number you work out from a square matrix (same number of rows and columns). It's written det A, or with straight bars | | instead of round brackets. If it's 0, the matrix has no inverse."],
  inv:["Inverse matrix","A⁻¹ is the matrix that undoes A: A⁻¹ × A gives the identity matrix I (1s down the diagonal, 0s everywhere else). It does for matrices what 1/a does for ordinary numbers."],
  el:["Elements","The numbers inside a matrix. Also called entries."],
  sys:["System of equations","Several equations that must all be true at the same time, for the same values of the unknowns."],
  gen:["General solution","When a system has infinitely many solutions, you describe all of them with one formula. Here x₃ and x₄ can be any numbers, and x₁ and x₂ then follow from them."],
  meq:["Matrix equation","An equation where the unknown is a whole matrix X. You solve it like an ordinary equation, with two matrix rules: there's no dividing (you multiply by an inverse instead), and the order of multiplying matters."],
  X:["Matrix X","An unknown 2×2 matrix. X⁻¹ is its inverse."]
};
/* A "See it" panel that steps through a list of {html, note}. */
const vizSteps=(note,fn)=>({
  steps:fn,
  html:()=>`${note?`<p class="sec-note">${note}</p>`:""}<div class="viz-box stp"><div class="stp-stage" id="stp-stage"></div><div class="stp-note" id="stp-note" aria-live="polite"></div><div class="btn-row"><button class="btn" id="stp-prev">← Back</button><button class="btn btn-primary" id="stp-next">Next step →</button><span class="small" id="stp-n"></span></div></div>`,
  setup:(p,c,ctx)=>{const S=fn(p,c);let i=0;const $=ctx.$;
    const show=()=>{$("#stp-stage").innerHTML=S[i].html;$("#stp-note").innerHTML=S[i].note||"";$("#stp-n").textContent=`Step ${i+1} of ${S.length}`;$("#stp-prev").disabled=i===0;$("#stp-next").disabled=i===S.length-1;};
    $("#stp-prev").addEventListener("click",()=>{if(i>0){i--;show();}});
    $("#stp-next").addEventListener("click",()=>{if(i<S.length-1){i++;show();}});
    show();}
});
function mulStepper(A,X,B,names){
  const P=mul(A,X),S=[];
  P.forEach((r,i)=>r.forEach((v,j)=>{
    const shown=P.map((rr,a)=>rr.map((w,b)=>(a<i||(a===i&&b<=j))?w:"?"));
    S.push({html:`${MX(A,{cls:a=>a===i?"hb":""})}${MX(X,{cls:(a,b)=>b===j?"hh":""})}<span>=</span>${MX(shown,{cls:(a,b)=>a===i&&b===j?"hl":shown[a][b]==="?"?"pend":""})}`,
      note:`Row ${i+1} of ${names[0]} times column ${j+1} of ${names[1]}: ${A[i].map((x,k)=>`${pn(x)} × ${pn(X[k][j])}`).join(" + ")} = <b>${nm(v)}</b>`});
  }));
  S.push({html:`${MX(P)}<span>+</span>${MX(B)}<span>=</span>${MX(madd(P,B),{cls:()=>"d3"})}`,note:`Add ${names[2]} number by number. You get exactly ${names[3]}, so ${names[1]} is right.`});
  return S;
}

/* ---------- the shared matrix A (tasks 1, 3, 4, 6) ---------- */
const EXAM_A=[[5,-5,-2],[-5,-4,-5],[-3,-1,4]];
let SHARED=null;
function randA(){for(;;){const A=[0,1,2].map(()=>[0,1,2].map(()=>rnz(-5,5)));const d=det(A);if(Math.abs(d)>=20&&Math.abs(d)<=400)return A;}}
const getA=()=>SHARED?SHARED.A:randA();
const SAME_A="On your exam sheet, tasks 1, 3, 4 and 6 all use the same matrix A, so det A from task 1 can be reused.";

/* ======================================================================
   Task 1: determinant of a 3×3 matrix
   ====================================================================== */
function calc1(p){const A=p.A,sub=[0,1,2].map(j=>minor(A,0,j)),M=sub.map(det2),terms=[A[0][0]*M[0],-A[0][1]*M[1],A[0][2]*M[2]];
  const down=[0,1,2].map(k=>A[0][k]*A[1][(k+1)%3]*A[2][(k+2)%3]),upd=[0,1,2].map(k=>A[2][k]*A[1][(k+1)%3]*A[0][(k+2)%3]);
  return {det:sum(terms),sub,M,terms,down,up:upd};}
function traps1(p,c){const A=p.A,Mp=c.sub.map(s=>s[0][0]*s[1][1]+s[0][1]*s[1][0]);
  return clean([
    [A[0][0]*c.M[0]+A[0][1]*c.M[1]+A[0][2]*c.M[2],"Check the signs in front of the three terms. They go +, −, +, so the middle one is subtracted."],
    [sum(c.down)+sum(c.up),"It looks like you added all six diagonal products. The three diagonals going up to the right are subtracted."],
    [sum(c.down),"That's only the three diagonals going down to the right. You still need to subtract the three going up."],
    [A[0][0]*Mp[0]-A[0][1]*Mp[1]+A[0][2]*Mp[2],"Check your 2×2 determinants: (top-left × bottom-right) <b>minus</b> (top-right × bottom-left)."],
    [A[0][0]*c.M[0]-A[0][1]*c.M[1]-A[0][2]*c.M[2],"The last term gets a plus sign. Along row 1 the signs go +, −, +."]
  ],c.det);}
const symMinor=(i,j)=>symM("a",3).filter((_,r)=>r!==i).map(row=>row.filter((_,k)=>k!==j));
const DET3_EQ=`${DET(A_)}${OP("=")}${en("a",1,1)}${DT(symMinor(0,0),{s:1})}${OP("−")}${en("a",1,2)}${DT(symMinor(0,1),{s:1})}${OP("+")}${en("a",1,3)}${DT(symMinor(0,2),{s:1})}`;
const DET2_EQ=`${DT([[mi("a"),mi("b")],[mi("c"),mi("d")]])}${OP("=")}${mi("a")}${mi("d")}${OP("−")}${mi("b")}${mi("c")}`;

const T1={
  id:"t1",topic:"Determinant 3×3",
  base:{A:EXAM_A,opts:[240,-240,-168,168,-266]},
  random:()=>{const p={A:getA()},c=calc1(p);p.opts=makeOpts(c.det,pmCands(c.det,traps1(p,c)));return p;},
  calc:calc1,
  text:(p,G,T)=>`Find det ${A_}, the ${T("det","determinant")} of the ${T("mx","matrix")}<span class="dmath">${A_} = ${MX(p.A,{cell:markCells([[1,1],[1,2],[1,3]],G,"a")})}</span>`,
  after:(p,c,done)=>OPTS(p,c.det,done),
  terms:{det:TERMS.det,mx:TERMS.mx},
  given:p=>[gEntry(p.A,1,1,{why:"The first number in row 1."}),gEntry(p.A,1,2,{why:"The second number in row 1."}),gEntry(p.A,1,3,{why:"The third number in row 1."})],
  find:[{sym:DET(A_),name:"the determinant of A",unit:"",why:"One number. That's the answer."}],
  parts:[Object.assign({id:"det",label:"Determinant of A",sym:DET(A_),unit:"",ans:(p,c)=>c.det,traps:traps1},EXACT)],
  idea:()=>`<p>For a 2×2 matrix the determinant is quick: (top-left × bottom-right) − (top-right × bottom-left).</p>
    <p>A 3×3 determinant is built from three of those. Go along the <b>first row</b>. For each of its three numbers:</p>
    <ol class="plain"><li>Cover up its row and its column. Four numbers are left over: a small 2×2 matrix.</li><li>Work out that 2×2 determinant.</li><li>Multiply it by the number you started with.</li></ol>
    <p>Then combine the three results with the signs <b>+ − +</b>: add the first, subtract the second, add the third.</p>
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>EQ(DET2_EQ)+EQ(DET3_EQ)+
    legend([[en("a",1,2),"the number in row 1, column 2 (first small number = row, second = column)",""],["| |","straight bars: the determinant of what's inside",""]],
      "Each small 2×2 is what's left of A after you cover the row and the column of the number in front of it."),
  plug:p=>{const A=p.A,s=[0,1,2].map(j=>minor(A,0,j));
    return EQ(`${DET(A_)}${OP("=")}${pn(A[0][0])}${OP("·")}${DT(s[0],{s:1})}${OP("−")}${pn(A[0][1])}${OP("·")}${DT(s[1],{s:1})}${OP("+")}${pn(A[0][2])}${OP("·")}${DT(s[2],{s:1})}`)+
      `<p>Work out each small 2×2 determinant first. For example: ${DT(s[0],{s:1})} = ${pn(s[0][0][0])} × ${pn(s[0][1][1])} − ${pn(s[0][0][1])} × ${pn(s[0][1][0])}.</p>`+
      watch("Minus a negative number is a plus: − (−5) = + 5. Put brackets around negative numbers so no minus sign gets lost.")+
      `<p class="tip"><b>Tip:</b> the answer box can do the arithmetic. For example <code>${A[0][0]}*((${s[0][0][0]})*(${s[0][1][1]})-(${s[0][0][1]})*(${s[0][1][0]}))</code> gives the first term.</p>`;},
  solution:(p,c)=>{const A=p.A;
    return steps([0,1,2].map(j=>[`Cover row 1 and column ${j+1}`,wk(MX(A,{s:1,cls:cross(0,j)}),CALC(`${DT(c.sub[j],{s:1})} = ${m2Line(c.sub[j])}`))]).concat([
      ["Combine with + − +",CALC(`${DET(A_)} = ${pn(A[0][0])} × ${pn(c.M[0])} − ${pn(A[0][1])} × ${pn(c.M[1])} + ${pn(A[0][2])} × ${pn(c.M[2])}`)+CALC(`= ${sumS(c.terms)} = <b>${nm(c.det)}</b>`)]
    ]))+checkline(`The diagonal shortcut (rule of Sarrus) gives the same. The three diagonals going down to the right: ${sumS(c.down)} = ${nm(sum(c.down))}. The three going up to the right: ${sumS(c.up)} = ${nm(sum(c.up))}. Down minus up: ${nm(sum(c.down))} − ${pn(sum(c.up))} = ${nm(c.det)} ✓`)+
    finalAns(`${DET(A_)} = ${nm(c.det)}`);},
  sheet:[
    {name:"2×2 determinant",eq:DET2_EQ,note:"Top-left × bottom-right, minus top-right × bottom-left."},
    {name:"3×3 determinant",eq:DET3_EQ,note:"Go along row 1 with the signs + − +. Each small determinant is what's left after covering that number's row and column."}
  ],
  takeEq:()=>DET3_EQ,
  takeaway:"Go along row 1. For each number: cover its row and column, find the 2×2 determinant that's left, multiply. Combine the three with + − +.",
  link:(p,c)=>`${optLine(p,c.det)} ${SAME_A.replace(" from task 1 can be reused",": write it down, you'll need it again")}`,
  viz:vizSteps("Step through the expansion along row 1, then the diagonal shortcut.",(p,c)=>{const A=p.A,S=[];let run=0;
    [0,1,2].forEach(j=>{run+=c.terms[j];S.push({html:`${MX(A,{cls:cross(0,j)})}<span>→</span>${DT(c.sub[j])}<span>= ${nm(c.M[j])}</span>`,
      note:`Cover row 1 and column ${j+1}. The 2×2 that's left is ${nm(c.M[j])}. Sign ${j===1?"−":"+"}, times ${pn(A[0][j])}: ${j===1?"−":"+"} ${pn(A[0][j])} × ${pn(c.M[j])} = ${nm(c.terms[j])}. Running total: <b>${nm(run)}</b>.`});});
    const ext=A.map(r=>r.concat([r[0],r[1]]));
    S.push({html:MX(ext,{cls:(i,j)=>{const k=j-i;return (k>=0&&k<=2?`d${k+1}`:"")+(j>2?" rep":"");}}),note:`The rule of Sarrus: copy columns 1 and 2 on the right. Multiply along the three diagonals going down to the right: ${sumS(c.down)} = ${nm(sum(c.down))}.`});
    S.push({html:MX(ext,{cls:(i,j)=>{const k=j-(2-i);return (k>=0&&k<=2?`d${k+1}`:"")+(j>2?" rep":"");}}),note:`Now the three going up to the right: ${sumS(c.up)} = ${nm(sum(c.up))}. Determinant = down − up = ${nm(sum(c.down))} − ${pn(sum(c.up))} = <b>${nm(c.det)}</b>.`});
    return S;})
};

/* ======================================================================
   Task 2: determinant of a 4×4 matrix (row 3 has two zeros)
   ====================================================================== */
function calc2(p){const A=p.A,m31=minor(A,2,0),m33=minor(A,2,2),w31=det3Lines(m31),w33=det3Lines(m33);
  const M21=det(minor(A,1,0)),M22=det(minor(A,1,1));
  return {det:A[2][0]*w31.d+A[2][2]*w33.d,m31,m33,w31,w33,M21,M22,chk:-A[1][0]*M21+A[1][1]*M22};}
function traps2(p,c){const A=p.A,t1=A[2][0]*c.w31.d,t3=A[2][2]*c.w33.d;
  return clean([
    [t1-t3,"Check the signs. Row 3 of the sign checkerboard reads + − + −, so columns 1 and 3 both get +."],
    [-t1+t3,"Both terms get a plus sign: in row 3, columns 1 and 3 are + squares on the checkerboard."],
    [t1,"Row 3 has two numbers that aren't zero, so you need two terms. You only have the one for column 1."],
    [t3,"Row 3 has two numbers that aren't zero, so you need two terms. You only have the one for column 3."],
    [A[1][0]*c.M21+A[1][1]*c.M22,"If you went along row 2: its signs are − + − +, so its first term is subtracted."]
  ],c.det);}
const T2={
  id:"t2",topic:"Determinant 4×4",level:"With zeros",
  blurb:"Like the sample sheet: row 3 has two zeros, so only two 3×3 determinants are needed.",
  base:{A:[[0,-1,3,-2],[1,2,0,0],[1,0,1,0],[2,-2,-1,1]],opts:[10,-11,12,-13,14]},
  random:()=>{const v=()=>pick([-2,-1,1,2,3]);for(;;){const A=[[0,v(),v(),v()],[v(),v(),0,0],[v(),0,v(),0],[v(),v(),v(),v()]],d=det(A);
    if(d!==0&&Math.abs(d)<=60){const p={A},c=calc2(p);p.opts=makeOpts(c.det,pmCands(c.det,traps2(p,c)));return p;}}},
  calc:calc2,
  text:(p,G,T)=>`Find the ${T("det","determinant")} of the 4×4 ${T("mx","matrix")}<span class="dmath">${A_} = ${MX(p.A,{cell:markCells([[3,1],[3,2],[3,3],[3,4]],G,"a")})}</span>`,
  after:(p,c,done)=>OPTS(p,c.det,done),
  terms:{det:TERMS.det,mx:TERMS.mx},
  given:p=>[1,2,3,4].map(j=>gEntry(p.A,3,j,{why:p.A[2][j-1]===0?"A zero in row 3.":"A number in row 3."})),
  find:[{sym:DET(A_),name:"the determinant of A",unit:"",why:"One number. That's the answer."}],
  parts:[Object.assign({id:"det",label:"Determinant of A",sym:DET(A_),unit:"",ans:(p,c)=>c.det,traps:traps2},EXACT)],
  idea:()=>`<p>A 4×4 determinant works like the 3×3 one, one size up. Pick a row. For each number in it, cover its row and its column: what's left is a 3×3 determinant, which you already know how to do. Multiply, then add everything up with the right signs.</p>
    <p>Two things make it much shorter:</p>
    <ul class="plain"><li>You may pick <b>any</b> row or column. Pick the one with the <b>most zeros</b>: zero times anything is zero, so those terms disappear. Row 3 has two zeros, so you only need two 3×3 determinants instead of four.</li>
    <li>Each term gets a sign from a checkerboard that starts with + in the top-left corner. Row 3 (highlighted) reads + − + −.</li></ul>
    ${signGrid(4,2)}
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>EQ(`${DET(A_)}${OP("=")}${en("a",3,1)}${Cf(3,1)}${OP("+")}${en("a",3,2)}${Cf(3,2)}${OP("+")}${en("a",3,3)}${Cf(3,3)}${OP("+")}${en("a",3,4)}${Cf(3,4)}`)+
    EQ(`${Cij}${OP("=")}(−1)<sup>${mi("i")}+${mi("j")}</sup>${OP("·")}${Mij}`)+
    legend([[Mij,"the 3×3 determinant left after you cover row i and column j",""],[Cij,"the same, with its sign from the checkerboard (called the cofactor)",""],[`(−1)<sup>${mi("i")}+${mi("j")}</sup>`,"+1 when i + j is even, −1 when it's odd: that's the checkerboard",""]],
      "Row 3 has zeros in columns 2 and 4, so two of the four terms are 0 and you can skip them."),
  plug:(p,c)=>{const A=p.A;
    return EQ(`${DET(A_)}${OP("=")}${pn(A[2][0])}${OP("·")}(+1)${OP("·")}${DT(c.m31,{s:1})}${OP("+")}0${OP("+")}${pn(A[2][2])}${OP("·")}(+1)${OP("·")}${DT(c.m33,{s:1})}${OP("+")}0`)+
      `<p>Each 3×3 determinant: go along its first row with + − +, exactly like task 1.</p>`;},
  solution:(p,c)=>{const A=p.A;
    return steps([
      ["Pick row 3",`Row 3 is (${A[2].map(nm).join(", ")}). Its zeros in columns 2 and 4 wipe out two terms. The checkerboard signs in row 3 are + − + −, so columns 1 and 3 both get +.`],
      ["Cover row 3 and column 1",wk(MX(A,{s:1,cls:cross(2,0)}))+det3Work(Mn(3,1),c.m31)],
      ["Cover row 3 and column 3",wk(MX(A,{s:1,cls:cross(2,2)}))+det3Work(Mn(3,3),c.m33)],
      ["Put it together",CALC(`${DET(A_)} = ${pn(A[2][0])} × ${pn(c.w31.d)} + ${pn(A[2][2])} × ${pn(c.w33.d)} = ${sumS([A[2][0]*c.w31.d,A[2][2]*c.w33.d])} = <b>${nm(c.det)}</b>`)]
    ])+checkline(`Going along row 2 instead (it also has two zeros, and its signs are − + − +): −${pn(A[1][0])} × ${pn(c.M21)} + ${pn(A[1][1])} × ${pn(c.M22)} = ${sumS([-A[1][0]*c.M21,A[1][1]*c.M22])} = ${nm(c.chk)} ✓`)+
    finalAns(`${DET(A_)} = ${nm(c.det)}`);},
  sheet:[
    {name:"Checkerboard signs",eq:MX([0,1,2,3].map(i=>[0,1,2,3].map(j=>sgn(i,j)>0?"+":"−")),{s:1}),note:"Row i, column j gets + when i + j is even and − when it's odd."},
    {name:"Expanding along a row",eq:`${DET(A_)}${OP("=")}${sb(mi("a"),`${mi("i")}1`)}${sb(mi("C"),`${mi("i")}1`)}${OP("+")}${sb(mi("a"),`${mi("i")}2`)}${sb(mi("C"),`${mi("i")}2`)}${OP("+")}…`,note:"Pick the row or column with the most zeros."}
  ],
  takeEq:()=>`${DET(A_)}${OP("=")}${en("a",3,1)}${Cf(3,1)}${OP("+")}${en("a",3,3)}${Cf(3,3)}`,
  takeaway:"Expand along the row or column with the most zeros, take each sign from the checkerboard, and do each 3×3 determinant like task 1.",
  link:(p,c)=>optLine(p,c.det),
  viz:vizSteps("Step through the expansion along row 3.",(p,c)=>{const A=p.A;return [
    {html:`${MX(A,{cls:i=>i===2?"hb":""})}${signGrid(4,2).replace('class="dmath"','')}`,note:"Row 3 has two zeros, so only two terms survive. Its signs on the checkerboard are + − + −."},
    {html:`${MX(A,{cls:cross(2,0)})}<span>→</span>${DT(c.m31)}<span>= ${nm(c.w31.d)}</span>`,note:`Cover row 3 and column 1. The 3×3 determinant left over is ${nm(c.w31.d)}. Sign +, times ${pn(A[2][0])}: ${nm(A[2][0]*c.w31.d)}.`},
    {html:`${MX(A,{cls:cross(2,2)})}<span>→</span>${DT(c.m33)}<span>= ${nm(c.w33.d)}</span>`,note:`Cover row 3 and column 3. The 3×3 determinant left over is ${nm(c.w33.d)}. Sign +, times ${pn(A[2][2])}: ${nm(A[2][2]*c.w33.d)}.`},
    {html:`${MX(A,{cls:(i,j)=>i===2&&(j===0||j===2)?"hl":i===2?"x":""})}<span>= ${sumS([A[2][0]*c.w31.d,A[2][2]*c.w33.d])} = ${nm(c.det)}</span>`,note:`Add the two terms (the zeros give nothing): det A = <b>${nm(c.det)}</b>.`}
  ];})
};

/* ======================================================================
   Task 2, full version: a 4×4 matrix with no zeros, so no shortcut.
   Expand along row 1: four 3×3 determinants, each done along its own row 1.
   ====================================================================== */
const S4=["+","−","+","−"];
function calc2f(p){const A=p.A,mins=[0,1,2,3].map(j=>minor(A,0,j)),ws=mins.map(det3Lines),M=ws.map(w=>w.d);
  const terms=M.map((v,j)=>sgn(0,j)*A[0][j]*v),R2=[0,1,2,3].map(j=>det(minor(A,1,j)));
  return {det:sum(terms),mins,ws,M,terms,R2,chkT:R2.map((v,j)=>sgn(1,j)*A[1][j]*v)};}
function traps2f(p,c){const A=p.A,t=c.terms;
  const d3=(m,f2,sg)=>[0,1,2].reduce((s,j)=>s+(sg?sg[j]:sgn(0,j))*m[0][j]*f2(minor(m,0,j)),0);
  const plus2=m=>m[0][0]*m[1][1]+m[0][1]*m[1][0];
  return clean([
    [sum(A[0].map((a,j)=>a*c.M[j])),"Check the signs in front of the four terms. Along row 1 they go + − + −, so terms 2 and 4 are subtracted."],
    [t[0]+t[1]+t[2]-t[3],"The fourth term gets a minus sign. Row 1 of the checkerboard reads + − + −."],
    [t[0]+t[1]+t[2],"Row 1 has four numbers, so you need four terms. Don't forget the one for column 4."],
    [t[1]+t[2]+t[3],"Row 1 has four numbers, so you need four terms. Don't forget the one for column 1."],
    [c.mins.reduce((s,m,j)=>s+sgn(0,j)*A[0][j]*d3(m,plus2),0),"Check your 2×2 determinants: (top-left × bottom-right) <b>minus</b> (top-right × bottom-left)."],
    [c.mins.reduce((s,m,j)=>s+sgn(0,j)*A[0][j]*d3(m,det2,[1,1,1]),0),"Inside each 3×3 determinant the signs also go + − +. The middle term there is subtracted too."]
  ],c.det);}
const symMinor4=j=>symM("a",4).slice(1).map(row=>row.filter((_,k)=>k!==j));
const DET4_EQ=`${DET(A_)}${OP("=")}${en("a",1,1)}${Mn(1,1)}${OP("−")}${en("a",1,2)}${Mn(1,2)}${OP("+")}${en("a",1,3)}${Mn(1,3)}${OP("−")}${en("a",1,4)}${Mn(1,4)}`;
const T2F={
  id:"t2f",topic:"Determinant 4×4",level:"Full expansion",
  blurb:"No zeros, so no shortcut: expand along row 1 and work out all four 3×3 determinants (twelve 2×2s in total).",
  base:{A:[[2,-1,3,1],[1,2,-2,3],[-1,3,1,2],[3,1,2,-1]],opts:[150,-20,-150,-80,-145]},
  random:()=>{const v=()=>pick([-3,-2,-1,1,2,3]);for(;;){const A=[0,1,2,3].map(()=>[0,1,2,3].map(v)),d=det(A);
    if(d!==0&&Math.abs(d)<=150){const p={A},c=calc2f(p);p.opts=makeOpts(c.det,pmCands(c.det,traps2f(p,c)));return p;}}},
  calc:calc2f,
  text:(p,G,T)=>`Find the ${T("det","determinant")} of the 4×4 ${T("mx","matrix")}<span class="dmath">${A_} = ${MX(p.A,{cell:markCells([[1,1],[1,2],[1,3],[1,4]],G,"a")})}</span>`,
  after:(p,c,done)=>OPTS(p,c.det,done),
  terms:{det:TERMS.det,mx:TERMS.mx},
  given:p=>[1,2,3,4].map(j=>gEntry(p.A,1,j,{why:`Number ${j} in row 1, the row you expand along.`})),
  find:[{sym:DET(A_),name:"the determinant of A",unit:"",why:"One number. That's the answer."}],
  parts:[Object.assign({id:"det",label:"Determinant of A",sym:DET(A_),unit:"",ans:(p,c)=>c.det,traps:traps2f},EXACT)],
  idea:()=>`<p>This matrix has no zeros, so there's no row that saves work. Do the full expansion along <b>row 1</b>:</p>
    <ol class="plain"><li>For each of the four numbers in row 1, cover its row and its column. What's left is a 3×3 determinant.</li>
    <li>Work out each 3×3 determinant exactly like task 1: along its own first row, with + − +.</li>
    <li>Multiply each one by the number you covered, and combine the four results with the signs <b>+ − + −</b> (row 1 of the checkerboard).</li></ol>
    ${signGrid(4,0)}
    <p>That's 4 three-by-three determinants, and 12 two-by-two determinants inside them. Write each one on its own line so no sign gets lost.</p>
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>EQ(DET4_EQ)+EQ(DET3_EQ)+EQ(DET2_EQ)+
    legend([[Mn(1,mi("j")),"the 3×3 determinant left after you cover row 1 and column j",""],["+ − + −","the checkerboard signs along row 1",""]],
      "Each 3×3 is split the same way into three 2×2 determinants with + − +."),
  plug:(p,c)=>{const A=p.A,D=j=>DT(c.mins[j],{s:1});
    return EQ(`${DET(A_)}${OP("=")}${pn(A[0][0])}${OP("·")}${D(0)}${OP("−")}${pn(A[0][1])}${OP("·")}${D(1)}`)+
      EQ(`${OP("+")}${pn(A[0][2])}${OP("·")}${D(2)}${OP("−")}${pn(A[0][3])}${OP("·")}${D(3)}`)+
      `<p>Now each 3×3 along its first row. For example the first one: ${DT(c.mins[0],{s:1})} = ${c.ws[0].l1}</p>`+
      watch("Two layers of signs: + − + − for the four big terms, and + − + inside every 3×3. Put brackets around negative numbers so a minus sign never disappears.");},
  solution:(p,c)=>{const A=p.A;
    return steps([
      ["Expand along row 1",`Row 1 is (${A[0].map(nm).join(", ")}). There are no zeros, so all four terms are needed. The checkerboard signs along row 1 are + − + −.`]
    ].concat([0,1,2,3].map(j=>[`Cover row 1 and column ${j+1} (sign ${S4[j]})`,
      wk(MX(A,{s:1,cls:cross(0,j)}))+det3Work(Mn(1,j+1),c.mins[j])+CALC(`term ${j+1}: ${S4[j]} ${pn(A[0][j])} × ${pn(c.M[j])} = <b>${nm(c.terms[j])}</b>`)
    ])).concat([
      ["Put it together",CALC(`${DET(A_)} = ${pn(A[0][0])} × ${pn(c.M[0])} − ${pn(A[0][1])} × ${pn(c.M[1])} + ${pn(A[0][2])} × ${pn(c.M[2])} − ${pn(A[0][3])} × ${pn(c.M[3])}`)+
        CALC(`= ${sumS(c.terms)} = <b>${nm(c.det)}</b>`)]
    ]))+checkline(`Going along row 2 instead (signs − + − +), its four 3×3 determinants are ${c.R2.map(nm).join(", ")}: −${pn(A[1][0])} × ${pn(c.R2[0])} + ${pn(A[1][1])} × ${pn(c.R2[1])} − ${pn(A[1][2])} × ${pn(c.R2[2])} + ${pn(A[1][3])} × ${pn(c.R2[3])} = ${sumS(c.chkT)} = ${nm(sum(c.chkT))} ✓`)+
    finalAns(`${DET(A_)} = ${nm(c.det)}`);},
  sheet:[
    {name:"4×4 full expansion",eq:DET4_EQ,note:"Along row 1 with + − + −. Each M is a 3×3 determinant, done like task 1."}
  ],
  takeEq:()=>DET4_EQ,
  takeaway:"With no zeros, expand along row 1: four 3×3 determinants with signs + − + −, each one split into three 2×2s with + − +.",
  link:(p,c)=>optLine(p,c.det),
  viz:vizSteps("Step through the full expansion along row 1.",(p,c)=>{const A=p.A,S=[{html:`${MX(A,{cls:i=>i===0?"hb":""})}${signGrid(4,0).replace('class="dmath"','')}`,note:"No zeros anywhere, so every term counts. Row 1 of the checkerboard reads + − + −."}];let run=0;
    [0,1,2,3].forEach(j=>{run+=c.terms[j];S.push({html:`${MX(A,{cls:cross(0,j)})}<span>→</span>${DT(c.mins[j])}<span>= ${nm(c.M[j])}</span>`,
      note:`Cover row 1 and column ${j+1}. The 3×3 left over is ${c.ws[j].l3} = ${nm(c.M[j])}. Sign ${S4[j]}, times ${pn(A[0][j])}: ${nm(c.terms[j])}. Running total: <b>${nm(run)}</b>.`});});
    return S;})
};

/* ======================================================================
   Task 3: sum of rows 1 and 2 of the inverse matrix
   ====================================================================== */
const NEED=[[0,0],[1,0],[2,0],[0,1],[1,1],[2,1]];  /* cofactors C_ij in columns 1 and 2: these become rows 1 and 2 of A⁻¹ */
function calc3(p){const A=p.A,w=det3Lines(A),C=cofM(A),Mi=minM(A),S=sum(NEED.map(([i,j])=>C[i][j]));return {det:w.d,w,C,Mi,S,ans:S/w.d};}
function traps3(p,c){const C=c.C,d=c.det;
  return clean([
    [(sum(C[0])+sum(C[1]))/d,"You used rows 1 and 2 of the cofactor matrix. Flip it first (transpose): row 1 of A⁻¹ is made from column 1 of the cofactors."],
    [c.S,"Don't forget to divide by det A at the end."],
    [c.S*d,"Divide by det A, don't multiply."],
    [sum(NEED.map(([i,j])=>c.Mi[i][j]))/d,"Some of these need a sign change. The cofactors follow the checkerboard + − + / − + − / + − +."],
    [msum(C)/d,"That's all three rows of A⁻¹. The question asks for rows 1 and 2 only."],
    [sum(p.A[0])+sum(p.A[1]),"That's from A itself. The question is about A⁻¹."]
  ],c.ans,0.004,0.001);}
const T3={
  id:"t3",topic:"Inverse matrix",
  base:{A:EXAM_A,opts:[-8.033,8.033,-0.383,0.383,3.308]},
  random:()=>{const p={A:getA()},c=calc3(p);p.opts=makeOpts(c.ans,pmCands(c.ans,traps3(p,c)));return p;},
  calc:calc3,
  text:(p,G,T)=>`Find the sum of the ${T("el","elements")} in the first two rows of ${INV(A_)}, the ${T("inv","inverse")} of the ${T("mx","matrix")}<span class="dmath">${A_} = ${MX(p.A,{cell:markCells([[1,1],[1,2],[1,3]],G,"a")})}</span>`,
  after:(p,c,done)=>OPTS(p,c.ans,done),
  terms:{el:TERMS.el,inv:TERMS.inv,mx:TERMS.mx},
  given:p=>[1,2,3].map(j=>gEntry(p.A,1,j,{why:"A number in row 1. You need det A first."})),
  find:[{sym:DET(A_),name:"the determinant of A",unit:"",why:"Part (a). You divide by it at the end."},{sym:mi("S"),name:"the sum of rows 1 and 2 of A⁻¹",unit:"",why:"Part (b). That's the answer."}],
  parts:[Object.assign({id:"det",label:"(a) det A",sym:DET(A_),unit:"",ans:(p,c)=>c.det,traps:(p)=>traps1(p,calc1(p))},EXACT),
    Object.assign({id:"s",label:"(b) Sum of the elements in rows 1 and 2 of A⁻¹",sym:mi("S"),unit:"",ans:(p,c)=>c.ans,traps:traps3},DEC)],
  idea:()=>`<p>The inverse A⁻¹ is the matrix that undoes A. For a 3×3 matrix you build it in three moves:</p>
    <ol class="plain"><li>Find det A, like in task 1. (If it were 0, there would be no inverse.)</li>
    <li>Replace each number by its <b>cofactor</b>: cover its row and column, find the 2×2 determinant that's left, and give it the sign from the checkerboard + − + / − + − / + − +.</li>
    <li>Flip that cofactor matrix across its diagonal (rows become columns), then divide everything by det A.</li></ol>
    <p><b>Shortcut:</b> after the flip, rows 1 and 2 of A⁻¹ are made from columns 1 and 2 of the cofactors. So you only need 6 cofactors, not all 9.</p>
    <p>${SAME_A}</p>
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>EQ(`${INV(A_)}${OP("=")}${FR("1",DET(A_))}${MX([[Cf(1,1),Cf(2,1),Cf(3,1)],[Cf(1,2),Cf(2,2),Cf(3,2)],[Cf(1,3),Cf(2,3),Cf(3,3)]],{cls:i=>i<2?"hb":""})}`)+
    EQ(`${Cij}${OP("=")}(−1)<sup>${mi("i")}+${mi("j")}</sup>${OP("·")}${Mij}`)+signGrid(3)+
    legend([[Cij,"the cofactor of the number in row i, column j",""],[Mij,"the 2×2 determinant left after you cover row i and column j",""]],
      "Look at the small numbers: C₂₁ sits in row 1, column 2. Everything is flipped across the diagonal. The highlighted rows 1 and 2 use C₁₁, C₂₁, C₃₁ and C₁₂, C₂₂, C₃₂."),
  plug:p=>{const A=p.A,ln=NEED.map(([i,j])=>`${Cf(i+1,j+1)}${OP("=")}${sgn(i,j)>0?"+":"−"}${DT(minor(A,i,j),{s:1})}`);
    return EQ(`${DET(A_)}${OP("=")}${pn(A[0][0])}${OP("·")}${DT(minor(A,0,0),{s:1})}${OP("−")}${pn(A[0][1])}${OP("·")}${DT(minor(A,0,1),{s:1})}${OP("+")}${pn(A[0][2])}${OP("·")}${DT(minor(A,0,2),{s:1})}`)+
      [0,2,4].map(k=>EQ(`${ln[k]}<span style="margin:0 1.2em"></span>${ln[k+1]}`)).join("")+
      EQ(`${mi("S")}${OP("=")}${FR(`${Cf(1,1)}${OP("+")}${Cf(2,1)}${OP("+")}${Cf(3,1)}${OP("+")}${Cf(1,2)}${OP("+")}${Cf(2,2)}${OP("+")}${Cf(3,2)}`,DET(A_))}`)+
      `<p class="tip"><b>Tip:</b> you can type the final division as a fraction, like <code>102/(-266)</code>.</p>`;},
  solution:(p,c)=>{const A=p.A,C=c.C,vals=NEED.map(([i,j])=>C[i][j]);
    return steps([
      ["Find det A (same as task 1)",CALC(`${DET(A_)} = ${c.w.l2}`)+CALC(`= ${c.w.l3} = <b>${nm(c.det)}</b>`)],
      ["The six cofactors you need",`<div class="cofs">${NEED.map(([i,j])=>`<p class="calc sm">${Cf(i+1,j+1)} = ${sgn(i,j)>0?"+":"−"}(${in2(minor(A,i,j))}) = ${nm(C[i][j])}</p>`).join("")}</div><p class="small">Cover row i and column j, take the 2×2 determinant, then use the checkerboard sign.</p>`],
      ["Rows 1 and 2 of A⁻¹",wk(`${INV(A_)} = ${FR("1",nm(c.det))}${MX([[C[0][0],C[1][0],C[2][0]],[C[0][1],C[1][1],C[2][1]],["…","…","…"]])}`)+`<p class="small">Row 1 is C₁₁, C₂₁, C₃₁ and row 2 is C₁₂, C₂₂, C₃₂: the flip.</p>`],
      ["Add them up and divide by det A",CALC(`${mi("S")} = (${sumS(vals)}) ÷ ${pn(c.det)} = ${nm(c.S)} ÷ ${pn(c.det)} = ${frH(c.S,c.det)}${approx(c.S,c.det)}`)]
    ])+checkline(`Row 1 of A⁻¹ times column 1 of A must give 1: (${pn(C[0][0])}×${pn(A[0][0])} + ${pn(C[1][0])}×${pn(A[1][0])} + ${pn(C[2][0])}×${pn(A[2][0])}) ÷ ${pn(c.det)} = ${nm(C[0][0]*A[0][0]+C[1][0]*A[1][0]+C[2][0]*A[2][0])} ÷ ${pn(c.det)} = 1 ✓<br>Times column 2 of A it must give 0: ${pn(C[0][0])}×${pn(A[0][1])} + ${pn(C[1][0])}×${pn(A[1][1])} + ${pn(C[2][0])}×${pn(A[2][1])} = ${nm(C[0][0]*A[0][1]+C[1][0]*A[1][1]+C[2][0]*A[2][1])} ✓`)+
    finalAns(`${DET(A_)} = ${nm(c.det)}, &nbsp;${mi("S")} = ${frH(c.S,c.det)}${approx(c.S,c.det)}`);},
  sheet:[
    {name:"Inverse of a 3×3 matrix",eq:`${INV(A_)}${OP("=")}${FR("1",DET(A_))}${MX([[Cf(1,1),Cf(2,1),Cf(3,1)],[Cf(1,2),Cf(2,2),Cf(3,2)],[Cf(1,3),Cf(2,3),Cf(3,3)]],{s:1})}`,note:"Cofactors, flipped across the diagonal, divided by det A."},
    {name:"Cofactor",eq:`${Cij}${OP("=")}(−1)<sup>${mi("i")}+${mi("j")}</sup>${Mij}`,note:"Cover row i and column j, take the 2×2 determinant, use the checkerboard sign."}
  ],
  takeEq:()=>`${INV(A_)}${OP("=")}${FR("1",DET(A_))}${OP("·")}(cofactors, flipped)`,
  takeaway:"Find det A, then the cofactors (2×2 determinant with a checkerboard sign), flip them across the diagonal and divide by det A. Rows 1 and 2 of A⁻¹ only need the cofactors from columns 1 and 2.",
  link:(p,c)=>`${optLine(p,c.ans)} The table on the exam is for the sum (part b).`,
  viz:vizSteps("Each cofactor is a 2×2 determinant with a sign. Watch where each one lands in A⁻¹: its row and column swap.",(p,c)=>{const A=p.A,S=[],filled={};
    NEED.forEach(([i,j])=>{filled[`${j}${i}`]=c.C[i][j];
      const grid=[0,1].map(r=>[0,1,2].map(k=>filled[`${r}${k}`]!==undefined?filled[`${r}${k}`]:"?"));
      S.push({html:`${MX(A,{cls:cross(i,j)})}<span>→</span>${DT(minor(A,i,j),{s:1})}<span>→</span><span>${FR("1",nm(c.det))}</span>${MX(grid,{cls:(r,k)=>r===j&&k===i?"hl":grid[r][k]==="?"?"pend":""})}`,
        note:`${Cf(i+1,j+1)}: cover row ${i+1} and column ${j+1}. The 2×2 determinant is ${nm(c.Mi[i][j])} and the checkerboard sign is ${sgn(i,j)>0?"+":"−"}, so ${Cf(i+1,j+1)} = ${nm(c.C[i][j])}. It goes to row ${j+1}, column ${i+1} of A⁻¹.`});});
    const grid=[0,1].map(r=>[0,1,2].map(k=>filled[`${r}${k}`]));
    S.push({html:`<span>${FR("1",nm(c.det))}</span>${MX(grid,{cls:()=>"hb"})}`,note:`Add all six: ${sumS(NEED.map(([i,j])=>c.C[i][j]))} = ${nm(c.S)}. Divide by det A = ${nm(c.det)}: <b>${frH(c.S,c.det)}${approx(c.S,c.det)}</b>.`});
    return S;})
};

/* ======================================================================
   Task 4: system of 3 equations, find xyz (Cramer's rule)
   ====================================================================== */
function calc4(p){const A=p.A,b=p.b,D=det(A),Ds=[0,1,2].map(j=>det(withCol(A,j,b))),xs=Ds.map(v=>v/D);
  return {D,Ds,xs,prod:xs[0]*xs[1]*xs[2],Dr:[0,1,2].map(i=>det(withRow(A,i,b)))};}
const ck4=A=>{for(let i=0;i<3;i++)for(let j=0;j<3;j++)if(Math.abs(A[i][j])===1)return [i,j];return [0,1];};
const trapsX=k=>(p,c)=>clean([
  [c.D/c.Ds[k],`Upside down: ${VN[k]} = Δ${VN[k]} ÷ Δ. The determinant with the swapped column goes on top.`],
  [c.Ds[k],"Divide by Δ = det A."],
  [c.Dr[k]/c.D,`Swap a column, not a row: Δ${VN[k]} is A with column ${k+1} (the ${VN[k]} column) replaced by the right-hand sides.`],
  [c.Ds[(k+1)%3]/c.D,`That's ${VN[(k+1)%3]}. For ${VN[k]}, replace column ${k+1}.`],
  [c.Ds[(k+2)%3]/c.D,`That's ${VN[(k+2)%3]}. For ${VN[k]}, replace column ${k+1}.`]
],c.xs[k]);
function traps4(p,c){return clean([
  [sum(c.xs),"That's x + y + z. The question asks for the product x · y · z."],
  [c.Ds[0]*c.Ds[1]*c.Ds[2],"Divide each Δ by Δ first, then multiply."],
  [c.Ds[0]*c.Ds[1]*c.Ds[2]/c.D,"Each of x, y and z needs its own division by Δ, so you divide by Δ three times."]
],c.prod);}
const eqLHS=(r,xs)=>r.map((a,j)=>`${pn(a)}·${pn(xs[j])}`).join(" + ");
const T4={
  id:"t4",topic:"System of equations",
  base:{A:EXAM_A,b:[31,26,-11],opts:[12,-12,16,-16,18]},
  random:()=>{const A=getA(),s=[rnz(-4,4),rnz(-4,4),rnz(-4,4)],p={A,b:A.map(r=>r[0]*s[0]+r[1]*s[1]+r[2]*s[2])},c=calc4(p);
    p.opts=makeOpts(c.prod,pmCands(c.prod,traps4(p,c)));return p;},
  calc:calc4,
  text:(p,G,T)=>{const k=ck4(p.A);return `Solve the ${T("sys","system of equations")}<span class="dmath">${SYS(p.A.map((r,i)=>({c:r,r:p.b[i]})),VX,G,{mark:(i,j)=>j<0?`b${i+1}`:(i===k[0]&&j===k[1]?`a${i+1}${j+1}`:null)})}</span>and find the product ${mi("x")}${mi("y")}${mi("z")}.`;},
  after:(p,c,done)=>OPTS(p,c.prod,done),
  terms:{sys:TERMS.sys},
  given:p=>{const [i,j]=ck4(p.A),v=p.A[i][j];
    return [1,2,3].map(n=>({k:`b${n}`,sym:sb(mi("b"),n),name:`right-hand side of equation ${n}`,unit:"",val:p.b[n-1],why:"The number after the = sign.",look:`Look after the = sign in equation ${n}.`,gtraps:p.b[n-1]<0?[[-p.b[n-1],"Keep the minus sign."]]:[]}))
      .concat([{k:`a${i+1}${j+1}`,sym:en("a",i+1,j+1),name:`number in front of ${VN[j]} in equation ${i+1}`,unit:"",val:v,
        why:`In the matrix A the row is the equation number and the column is the unknown (x, y, z). So this is row ${i+1}, column ${j+1}.`,
        look:Math.abs(v)===1?`"${v<0?"−":""}${VN[j]}" with no number in front means ${nm(v)} · ${VN[j]}.`:`The number in front of ${VN[j]} in equation ${i+1}, with its sign.`,
        gtraps:(v<0?[[-v,"Keep the minus sign in front of it."]]:[]).concat(Math.abs(v)===1?[[0,`A letter on its own still counts: ${v<0?"−":""}${VN[j]} means ${nm(v)} · ${VN[j]}.`]]:[])}]);},
  find:[{sym:mi("x"),name:"x",unit:"",why:"Part (a)."},{sym:mi("y"),name:"y",unit:"",why:"Part (b)."},{sym:mi("z"),name:"z",unit:"",why:"Part (c)."},{sym:`${mi("x")}${mi("y")}${mi("z")}`,name:"the product",unit:"",why:"Part (d). That's the answer: x times y times z."}],
  parts:[0,1,2].map(k=>Object.assign({id:VN[k],label:`(${"abc"[k]}) ${VN[k]}`,sym:VX[k],unit:"",ans:(p,c)=>c.xs[k],traps:trapsX(k)},EXACT))
    .concat([Object.assign({id:"xyz",label:"(d) The product xyz",sym:`${mi("x")}${mi("y")}${mi("z")}`,unit:"",ans:(p,c)=>c.prod,traps:traps4},EXACT)]),
  idea:()=>`<p>Write the system with matrices. The numbers in front of x, y and z make a 3×3 matrix A (one row per equation, one column per unknown). The numbers after the = signs make a column b.</p>
    <p><b>Cramer's rule</b> then gives each unknown as one determinant divided by another:</p>
    <ul class="plain"><li>Bottom, the same every time: Δ = det A.</li><li>Top for x: Δx, the determinant of A with column 1 (the x column) swapped for the column b. For y swap column 2, for z swap column 3.</li></ul>
    <p>So it's four 3×3 determinants, each done like task 1. ${SAME_A.replace("det A from task 1","Δ = det A")}</p>
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>{const S=symM("a",3),bs=[1,2,3].map(i=>sb(mi("b"),i)),hh=k=>(i,j)=>j===k?"hh":"";
    return EQ(`${mi("x")}${OP("=")}${FR(DEL(mi("x")),DEL())},<span style="margin:0 .7em"></span>${mi("y")}${OP("=")}${FR(DEL(mi("y")),DEL())},<span style="margin:0 .7em"></span>${mi("z")}${OP("=")}${FR(DEL(mi("z")),DEL())}`)+
      EQ(`${DEL()}${OP("=")}${DT(S,{s:1})}<span style="margin:0 .7em"></span>${DEL(mi("x"))}${OP("=")}${DT(withCol(S,0,bs),{s:1,cls:hh(0)})}`)+
      EQ(`${DEL(mi("y"))}${OP("=")}${DT(withCol(S,1,bs),{s:1,cls:hh(1)})}<span style="margin:0 .7em"></span>${DEL(mi("z"))}${OP("=")}${DT(withCol(S,2,bs),{s:1,cls:hh(2)})}`)+
      legend([[DEL(),"det A: the numbers in front of x, y and z",""],[DEL(mi("x")),"det A with column 1 replaced by b₁, b₂, b₃ (shaded)",""],[sb(mi("b"),"1"),"the right-hand side of equation 1",""]]);},
  plug:p=>{const A=p.A,b=p.b,hh=k=>(i,j)=>j===k?"hh":"";
    return EQ(`${DEL()}${OP("=")}${DT(A,{s:1})}<span style="margin:0 .7em"></span>${DEL(mi("x"))}${OP("=")}${DT(withCol(A,0,b),{s:1,cls:hh(0)})}`)+
      EQ(`${DEL(mi("y"))}${OP("=")}${DT(withCol(A,1,b),{s:1,cls:hh(1)})}<span style="margin:0 .7em"></span>${DEL(mi("z"))}${OP("=")}${DT(withCol(A,2,b),{s:1,cls:hh(2)})}`)+
      `<p>Work out each one along its first row (+ − +), then x = Δx ÷ Δ, y = Δy ÷ Δ, z = Δz ÷ Δ.</p>`;},
  solution:(p,c)=>{const A=p.A,b=p.b,hh=k=>(i,j)=>j===k?"hh":"";
    const one=(lab,m,cls)=>{const w=det3Lines(m);return wk(`${lab} = ${DT(m,{s:1,cls})}`)+CALC(`= ${w.l2}`)+CALC(`= ${w.l3} = <b>${nm(w.d)}</b>`);};
    return steps([
      ["Δ = det A (same as task 1)",one(DEL(),A)],
      ["Δx: swap column 1 for b",one(DEL(mi("x")),withCol(A,0,b),hh(0))],
      ["Δy: swap column 2 for b",one(DEL(mi("y")),withCol(A,1,b),hh(1))],
      ["Δz: swap column 3 for b",one(DEL(mi("z")),withCol(A,2,b),hh(2))],
      ["Divide",CALC(`${mi("x")} = ${nm(c.Ds[0])} ÷ ${pn(c.D)} = <b>${nm(c.xs[0])}</b>, &nbsp;${mi("y")} = ${nm(c.Ds[1])} ÷ ${pn(c.D)} = <b>${nm(c.xs[1])}</b>, &nbsp;${mi("z")} = ${nm(c.Ds[2])} ÷ ${pn(c.D)} = <b>${nm(c.xs[2])}</b>`)],
      ["Multiply",CALC(`${mi("x")}${mi("y")}${mi("z")} = ${pn(c.xs[0])} × ${pn(c.xs[1])} × ${pn(c.xs[2])} = <b>${nm(c.prod)}</b>`)]
    ])+checkline(`Put them back into the equations:<br>${A.map((r,i)=>`Equation ${i+1}: ${eqLHS(r,c.xs)} = ${nm(sum(r.map((a,j)=>a*c.xs[j])))} = ${nm(b[i])} ✓`).join("<br>")}`)+
    finalAns(`${mi("x")} = ${nm(c.xs[0])}, &nbsp;${mi("y")} = ${nm(c.xs[1])}, &nbsp;${mi("z")} = ${nm(c.xs[2])}, &nbsp;${mi("x")}${mi("y")}${mi("z")} = ${nm(c.prod)}`);},
  sheet:[{name:"Cramer's rule",eq:`${mi("x")}${OP("=")}${FR(DEL(mi("x")),DEL())},${OP("")}${mi("y")}${OP("=")}${FR(DEL(mi("y")),DEL())},${OP("")}${mi("z")}${OP("=")}${FR(DEL(mi("z")),DEL())}`,note:"Δ = det A. Δx = det A with column 1 replaced by the right-hand sides (column 2 for y, column 3 for z)."}],
  takeEq:()=>`${mi("x")}${OP("=")}${FR(DEL(mi("x")),DEL())}`,
  takeaway:"Δ is det A. For each unknown, swap its column for the right-hand sides, take that determinant and divide by Δ.",
  link:(p,c)=>`${optLine(p,c.prod)} The table on the exam is for the product xyz.`,
  viz:{
    html:()=>`<p class="sec-note">Each equation is a flat plane in 3D. The solution is the one point where all three planes meet. Drag to turn it.</p>
      <div class="viz-box"><canvas class="plane-cv" id="pl-cv" role="img" aria-label="Three planes meeting at one point"></canvas>
      <div class="key"><span><i style="background:var(--blue)"></i>equation 1</span><span><i style="background:var(--heat)"></i>equation 2</span><span><i style="background:var(--ok)"></i>equation 3</span></div>
      <div class="btn-row"><button class="btn" id="pl-play">Pause</button></div></div>`,
    setup:(p,c,ctx)=>planes3D(ctx,p.A,c.xs)
  }
};
function planes3D(ctx,A,P){
  const cv=ctx.$("#pl-cv");if(!cv||!cv.getContext)return;const g=cv.getContext("2d");if(!g)return;
  const W=600,H=330,cs=getComputedStyle(document.documentElement),col=(n,d)=>cs.getPropertyValue(n).trim()||d;
  const K={ink:col("--ink","#14244a"),ink2:col("--ink-2","#55637f"),rule:col("--rule","#d3dbe8"),card:col("--card","#fff"),f:[col("--blue","#2346a8"),col("--heat","#d4602a"),col("--ok","#16714a")]};
  const nrm=v=>{const l=Math.hypot(v[0],v[1],v[2])||1;return v.map(x=>x/l);},crs=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
  const s=Math.max(3.5,0.55*Math.max(4,Math.max(...P.map(Math.abs))+2));
  const patches=A.map(n=>{const nn=nrm(n),e=Math.abs(nn[0])<0.8?[1,0,0]:[0,1,0],u=nrm(crs(nn,e)),v=nrm(crs(nn,u));return [[1,1],[1,-1],[-1,-1],[-1,1]].map(([a,b])=>P.map((x,k)=>x+s*(a*u[k]+b*v[k])));});
  const segs=[[0,1],[1,2],[0,2]].map(([i,j])=>{const d=nrm(crs(A[i],A[j]));return [P.map((x,k)=>x-s*d[k]),P.map((x,k)=>x+s*d[k])];});
  const L=Math.max(4,Math.max(...P.map(Math.abs))+2),ctr=P.map(x=>x/2),Rb=Math.hypot(...ctr)+Math.max(L,s*1.5)+1,Kz=Math.min(W,H)*0.46/Rb;
  let th=0.75,ph=0.42,playing=!ctx.reduceMotion,drag=null,scale=1;
  const proj=v=>{const x=v[0]-ctr[0],y=v[1]-ctr[1],z=v[2]-ctr[2];const x1=x*Math.cos(th)-y*Math.sin(th),y1=x*Math.sin(th)+y*Math.cos(th);
    return [W/2+x1*Kz,H/2-(z*Math.cos(ph)-y1*Math.sin(ph))*Kz,z*Math.sin(ph)+y1*Math.cos(ph)];};
  const size=()=>{const w=Math.max(1,cv.getBoundingClientRect().width),dpr=Math.min(2,window.devicePixelRatio||1);cv.width=Math.round(w*dpr);cv.height=Math.round(w*H/W*dpr);scale=cv.width/W;};
  const line=(a,b,c,w,dash)=>{const A1=proj(a),B1=proj(b);g.beginPath();g.moveTo(A1[0],A1[1]);g.lineTo(B1[0],B1[1]);g.strokeStyle=c;g.lineWidth=w;g.setLineDash(dash||[]);g.stroke();g.setLineDash([]);};
  const draw=()=>{g.setTransform(1,0,0,1,0,0);g.clearRect(0,0,cv.width,cv.height);g.setTransform(scale,0,0,scale,0,0);
    g.font='italic 15px "STIX Two Text",Cambria,serif';g.textAlign="center";g.textBaseline="middle";
    [[1,0,0,"x"],[0,1,0,"y"],[0,0,1,"z"]].forEach(([a,b,c,n])=>{const e=[a*L,b*L,c*L];line(e.map(x=>-x),e,K.rule,1.4);const q=proj(e.map(x=>x*1.08));g.fillStyle=K.ink2;g.fillText(n,q[0],q[1]);});
    patches.map((pts,i)=>({i,pts,d:sum(pts.map(q=>proj(q)[2]))/4})).sort((a,b)=>b.d-a.d).forEach(({i,pts})=>{
      g.beginPath();pts.forEach((q,k)=>{const r=proj(q);k?g.lineTo(r[0],r[1]):g.moveTo(r[0],r[1]);});g.closePath();
      g.globalAlpha=0.2;g.fillStyle=K.f[i];g.fill();g.globalAlpha=0.85;g.strokeStyle=K.f[i];g.lineWidth=1.6;g.stroke();g.globalAlpha=1;});
    segs.forEach(([a,b])=>line(a,b,K.ink2,1.2,[4,4]));
    const q=proj(P);g.beginPath();g.arc(q[0],q[1],5.5,0,Math.PI*2);g.fillStyle=K.ink;g.fill();
    const lab=`(${P.map(nm).join(", ")})`;g.font='600 14px "Atkinson Hyperlegible",system-ui,sans-serif';const tw=g.measureText(lab).width+12;
    g.fillStyle=K.card;g.strokeStyle=K.ink2;g.lineWidth=1;g.beginPath();if(g.roundRect)g.roundRect(q[0]+10,q[1]-24,tw,22,4);else g.rect(q[0]+10,q[1]-24,tw,22);g.fill();g.stroke();
    g.fillStyle=K.ink;g.textAlign="left";g.fillText(lab,q[0]+16,q[1]-13);};
  size();draw();
  const btn=ctx.$("#pl-play");if(btn){btn.textContent=playing?"Pause":"Turn";btn.addEventListener("click",()=>{playing=!playing;btn.textContent=playing?"Pause":"Turn";});}
  cv.addEventListener("pointerdown",e=>{drag={x:e.clientX,y:e.clientY,th,ph};try{cv.setPointerCapture(e.pointerId);}catch(_){};});
  cv.addEventListener("pointermove",e=>{if(!drag)return;th=drag.th+(e.clientX-drag.x)*0.01;ph=Math.max(-1.3,Math.min(1.3,drag.ph+(e.clientY-drag.y)*0.01));draw();});
  const end=()=>{drag=null;};cv.addEventListener("pointerup",end);cv.addEventListener("pointercancel",end);
  let last=0;ctx.loop(dt=>{last+=dt;if(Math.abs(cv.getBoundingClientRect().width*Math.min(2,window.devicePixelRatio||1)-cv.width)>2)size();if(playing&&!drag){th+=dt*0.35;draw();}else if(last>0.5){last=0;draw();}});
}

/* ======================================================================
   Task 5: 2×2 matrix equation AX + B = C
   ====================================================================== */
function calc5(p){const D=det2(p.A),CB=msub(p.C,p.B),adj=adj2(p.A),P=mul(adj,CB),X=P.map(r=>r.map(v=>v/D));return {D,CB,adj,P,X,S:msum(X)};}
function traps5(p,c){const A=p.A;return clean([
  [msum(mul(c.CB,c.adj))/c.D,"Order matters with matrices. A is on the left of X, so A⁻¹ goes on the left too: X = A⁻¹(C − B), not (C − B)A⁻¹."],
  [msum(mul(c.adj,madd(p.C,p.B)))/c.D,"When B moves to the other side it becomes − B: use C − B, not C + B."],
  [msum(mul(c.adj,p.C))/c.D,"Subtract B from C first: AX = C − B."],
  [msum(c.P),"Don't forget to divide by det A (the 1/det A in front of the inverse)."],
  [msum(mul([[A[0][0],-A[0][1]],[-A[1][0],A[1][1]]],c.CB))/c.D,"In the 2×2 inverse, swap the two numbers on the main diagonal (top-left and bottom-right)."],
  [msum(mul([[A[1][1],A[0][1]],[A[1][0],A[0][0]]],c.CB))/c.D,"In the 2×2 inverse, the other two numbers change sign."]
],c.S,0.004,0.001);}
const INV2_EQ=`${MX([[mi("a"),mi("b")],[mi("c"),mi("d")]])}<sup>−1</sup>${OP("=")}${FR("1",`${mi("a")}${mi("d")}${OP("−")}${mi("b")}${mi("c")}`)}${MX([[mi("d"),`−${mi("b")}`],[`−${mi("c")}`,mi("a")]])}`;
const MUL2_EQ=`${MX([[mi("p"),mi("q")],[mi("r"),mi("s")]])}${MX([[mi("e"),mi("f")],[mi("g"),mi("h")]])}${OP("=")}${MX([[`${mi("p")}${mi("e")}+${mi("q")}${mi("g")}`,`${mi("p")}${mi("f")}+${mi("q")}${mi("h")}`],[`${mi("r")}${mi("e")}+${mi("s")}${mi("g")}`,`${mi("r")}${mi("f")}+${mi("s")}${mi("h")}`]])}`;
const SOLVE_EQ=`${A_}${X_}${OP("+")}${B_}${OP("=")}${C_}${IMPLIES}${X_}${OP("=")}${INV(A_)}(${C_}${OP("−")}${B_})`;
const T5={
  id:"t5",topic:"Matrix equation 2×2",
  base:{A:[[1,6],[3,-4]],B:[[1,2],[4,-3]],C:[[-14,-24],[3,29]],opts:[10,2,-8,11,-7]},
  random:()=>{for(;;){const A=[[rnz(-6,6),rnz(-6,6)],[rnz(-6,6),rnz(-6,6)]],D=det2(A);if(D===0||Math.abs(D)>40)continue;
    const X=[[rnz(-5,5),rnz(-5,5)],[rnz(-5,5),rnz(-5,5)]],B=[[rnz(-5,5),rnz(-5,5)],[rnz(-5,5),rnz(-5,5)]],C=madd(mul(A,X),B);
    if(C.flat().some(v=>Math.abs(v)>60))continue;const p={A,B,C},c=calc5(p);p.opts=makeOpts(c.S,pmCands(c.S,traps5(p,c)));return p;}},
  calc:calc5,
  text:(p,G,T)=>`Solve the ${T("meq","matrix equation")}<span class="dmath">${MX(p.A,{cell:markCells([[1,1],[1,2],[2,1],[2,2]],G,"a")})}${OP("·")}${X_}${OP("+")}${MX(p.B)}${OP("=")}${MX(p.C)}</span>Call the three matrices ${A_} (in front of ${X_}), ${B_} and ${C_}, so the equation is ${A_}${X_} + ${B_} = ${C_}. Find the sum of all the ${T("el","elements")} of ${X_}.`,
  after:(p,c,done)=>OPTS(p,c.S,done),
  terms:{meq:TERMS.meq,el:TERMS.el},
  given:p=>[[1,1,"Top-left of A."],[1,2,"Top-right of A."],[2,1,"Bottom-left of A."],[2,2,"Bottom-right of A."]].map(([i,j,w])=>gEntry(p.A,i,j,{of:"A",why:w})),
  find:[{sym:DET(A_),name:"the determinant of A",unit:"",why:"Part (a). You need it for A⁻¹."},{sym:mi("S"),name:"the sum of all elements of X",unit:"",why:"Part (b). That's the answer."}],
  parts:[Object.assign({id:"det",label:"(a) det A",sym:DET(A_),unit:"",ans:(p,c)=>c.D,traps:p=>{const A=p.A;return clean([[A[0][0]*A[1][1]+A[0][1]*A[1][0],"It's (top-left × bottom-right) minus (top-right × bottom-left)."],[A[0][0]*A[0][1]-A[1][0]*A[1][1],"Multiply along the two diagonals, not along the rows."]],det2(A));}},EXACT),
    Object.assign({id:"s",label:"(b) Sum of all the elements of X",sym:mi("S"),unit:"",ans:(p,c)=>c.S,traps:traps5},EXACT)],
  idea:()=>`<p>Solve it like the ordinary equation a·x + b = c:</p>
    <ol class="plain"><li>Move B to the other side: AX = C − B. (Subtract the numbers in matching places.)</li>
    <li>Get rid of A. Matrices can't be divided, so you multiply both sides by the inverse A⁻¹ instead. It has to go on the <b>left</b>, because A is on the left of X, and with matrices the order of multiplying matters: X = A⁻¹(C − B).</li></ol>
    <p>A 2×2 inverse is quick: swap the two numbers on the main diagonal (top-left and bottom-right), change the signs of the other two, and divide everything by the determinant.</p>
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>EQ(SOLVE_EQ)+EQ(INV2_EQ)+EQ(MUL2_EQ)+
    legend([[INV(A_),"the inverse of A",""],[`${mi("a")}${mi("d")}${OP("−")}${mi("b")}${mi("c")}`,"det A, the determinant",""]],"Multiplying matrices: each answer number is a row of the left matrix times a column of the right one. Multiply the matching pairs and add."),
  plug:p=>{const A=p.A;
    return EQ(`${C_}${OP("−")}${B_}${OP("=")}${MX(p.C.map((r,i)=>r.map((v,j)=>`${nm(v)} − ${pn(p.B[i][j])}`)))}`)+
      EQ(`${INV(A_)}${OP("=")}${FR("1",`${pn(A[0][0])}·${pn(A[1][1])} − ${pn(A[0][1])}·${pn(A[1][0])}`)}${MX(adj2(A))}`)+
      EQ(`${X_}${OP("=")}${INV(A_)}(${C_}${OP("−")}${B_})`)+
      `<p class="tip"><b>Tip:</b> keep the 1/det A in front. Multiply the whole numbers first and divide at the very end.</p>`;},
  solution:(p,c)=>{const A=p.A;
    return steps([
      ["Move B over: C − B",wk(`${C_} − ${B_} = ${MX(c.CB)}`)],
      ["det A",CALC(`${DET(A_)} = ${pn(A[0][0])} × ${pn(A[1][1])} − ${pn(A[0][1])} × ${pn(A[1][0])} = ${nm(A[0][0]*A[1][1])} − ${pn(A[0][1]*A[1][0])} = <b>${nm(c.D)}</b>`)],
      ["The inverse",wk(`${INV(A_)} = ${FR("1",nm(c.D))}${MX(c.adj)}`)+`<p class="small">Swap ${nm(A[0][0])} and ${nm(A[1][1])}; change the signs of ${nm(A[0][1])} and ${nm(A[1][0])}.</p>`],
      ["Multiply (row × column)",wk(`${MX(c.adj)}${MX(c.CB)} = ${MX(c.P)}`)+lines(prodLines(c.adj,c.CB,c.P))],
      ["Divide by det A",wk(`${X_} = ${FR("1",nm(c.D))}${MX(c.P)} = ${MX(c.X)}`)],
      ["Add the elements",CALC(`${sumS(c.X.flat())} = <b>${nm(c.S)}</b>`)]
    ])+checkline(`${A_}${X_} = ${MX(mul(A,c.X),{s:1})}, and adding ${B_} gives ${MX(madd(mul(A,c.X),p.B),{s:1})}, which is ${C_} ✓`)+
    finalAns(`${DET(A_)} = ${nm(c.D)}, &nbsp;${X_} = ${MX(c.X,{s:1})}, &nbsp;sum = ${nm(c.S)}`);},
  sheet:[{name:"Solving AX + B = C",eq:SOLVE_EQ,note:"A⁻¹ goes on the same side as A (the left)."},{name:"2×2 inverse",eq:INV2_EQ,note:"Swap the diagonal, change the signs of the other two, divide by the determinant."}],
  takeEq:()=>SOLVE_EQ,
  takeaway:"Move B across (C − B), then multiply by A⁻¹ on the left. A 2×2 inverse: swap the diagonal, flip the other two signs, divide by det A.",
  link:(p,c)=>`${optLine(p,c.S)} The table on the exam is for the sum (part b).`,
  viz:vizSteps("Check the answer: multiply A by your X, row by column, then add B. You should land exactly on C.",p=>{const c=calc5(p);return mulStepper(p.A,c.X,p.B,["A","X","B","C"]);})
};

/* ======================================================================
   Task 6: 3×3 matrix equation AX + B = C (X is 3×2)
   ====================================================================== */
function calc6(p){const w=det3Lines(p.A),d=w.d,Co=cofM(p.A),adj=tr(Co),CB=msub(p.C,p.B),P=mul(adj,CB),X=P.map(r=>r.map(v=>v/d));return {det:d,w,Co,adj,CB,P,X,S:msum(X)};}
function traps6(p,c){return clean([
  [msum(mul(c.adj,p.C))/c.det,"Subtract B from C first: AX = C − B."],
  [msum(mul(c.adj,madd(p.C,p.B)))/c.det,"When B moves across it becomes − B: use C − B, not C + B."],
  [msum(mul(c.Co,c.CB))/c.det,"The cofactor matrix has to be flipped across its diagonal before it becomes the inverse."],
  [msum(c.P),"Don't forget to divide by det A at the end."]
],c.S,0.004,0.001);}
const T6={
  id:"t6",topic:"Matrix equation 3×3",
  base:{A:EXAM_A,B:[[3,5],[2,-3],[3,4]],C:[[39,-23],[23,-13],[-11,-2]],opts:[-3,-1,0,1,-2]},
  random:()=>{for(;;){const A=getA(),X=[0,1,2].map(()=>[rnz(-5,5),rnz(-5,5)]),B=[0,1,2].map(()=>[rnz(-5,5),rnz(-5,5)]),C=madd(mul(A,X),B);
    if(C.flat().some(v=>Math.abs(v)>90))continue;const p={A,B,C},c=calc6(p);
    p.opts=makeOpts(c.S,shuffle([c.S-1,c.S+1,c.S+2,c.S-2]).concat(traps6(p,c).map(t=>t[0])));return p;}},
  calc:calc6,
  text:(p,G,T)=>`Solve the ${T("meq","matrix equation")}<span class="dmath">${MX(p.A)}${OP("·")}${X_}${OP("+")}${MX(p.B,{cell:markCells([[1,1],[1,2]],G,"b")})}${OP("=")}${MX(p.C,{cell:markCells([[1,1],[1,2]],G,"c")})}</span>Call the three matrices ${A_}, ${B_} and ${C_}, so the equation is ${A_}${X_} + ${B_} = ${C_}. Find the sum of all the ${T("el","elements")} of ${X_}.`,
  after:(p,c,done)=>OPTS(p,c.S,done),
  terms:{meq:TERMS.meq,el:TERMS.el},
  given:p=>[gEntry(p.B,1,1,{l:"b",of:"B",why:"Top-left of B, the matrix that's added."}),gEntry(p.B,1,2,{l:"b",of:"B",why:"Top-right of B."}),gEntry(p.C,1,1,{l:"c",of:"C",why:"Top-left of C, the matrix after the = sign."}),gEntry(p.C,1,2,{l:"c",of:"C",why:"Top-right of C."})],
  find:[{sym:sb(mi("x"),"11"),name:"the top-left element of X",unit:"",why:"Part (a). A first check."},{sym:mi("S"),name:"the sum of all elements of X",unit:"",why:"Part (b). That's the answer."}],
  parts:[Object.assign({id:"x11",label:"(a) The top-left element of X",sym:sb(mi("x"),"11"),unit:"",ans:(p,c)=>c.X[0][0],traps:(p,c)=>clean([[c.P[0][0],"Divide by det A."],[mul(c.Co,c.CB)[0][0]/c.det,"Flip the cofactor matrix across its diagonal first."],[mul(c.adj,p.C)[0][0]/c.det,"Use C − B, not C."]],c.X[0][0],0.004,0.001)},EXACT),
    Object.assign({id:"s",label:"(b) Sum of all the elements of X",sym:mi("S"),unit:"",ans:(p,c)=>c.S,traps:traps6},EXACT)],
  idea:()=>`<p>Same plan as task 5: move B over, then multiply by A⁻¹ on the left: X = A⁻¹(C − B). X has 3 rows and 2 columns, like B and C.</p>
    <p>A is 3×3 this time, so build A⁻¹ with the cofactor method from task 3, using all nine cofactors: A⁻¹ = (1/det A) × (the cofactor matrix, flipped across its diagonal).</p>
    <p><b>Tip:</b> keep the 1/det A in front until the very end. Multiply the flipped cofactor matrix by (C − B) using whole numbers, then divide once.</p>
    <p>${SAME_A}</p>
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>EQ(SOLVE_EQ)+EQ(`${X_}${OP("=")}${FR("1",DET(A_))}${OP("·")}<span class="mu">adj</span>&#8202;${A_}${OP("·")}(${C_}${OP("−")}${B_})`)+
    legend([[`<span class="mu">adj</span>&#8202;${A_}`,"the cofactor matrix of A, flipped across its diagonal (task 3)",""]],"A 3×3 matrix times a 3×2 matrix gives a 3×2 matrix. Each element is a row of the left matrix times a column of the right one: three products, added."),
  plug:p=>{const A=p.A;
    return EQ(`${C_}${OP("−")}${B_}${OP("=")}${MX(p.C.map((r,i)=>r.map((v,j)=>`${nm(v)} − ${pn(p.B[i][j])}`)))}`)+
      `<p>The nine cofactors (cover row i and column j, take the 2×2 determinant, use the checkerboard sign):</p>`+
      `<div class="eq-wrap"><div class="eq" style="text-align:left;font-size:1.05rem">${MX([0,1,2].map(i=>[0,1,2].map(j=>`${sgn(i,j)>0?"+":"−"}(${in2(minor(A,i,j))})`)))}</div></div>`+
      EQ(`${X_}${OP("=")}${FR("1",DET(A_))}${OP("·")}<span class="mu">adj</span>&#8202;${A_}${OP("·")}(${C_}${OP("−")}${B_})`);},
  solution:(p,c)=>{const A=p.A;
    return steps([
      ["Move B over: C − B",wk(`${C_} − ${B_} = ${MX(c.CB)}`)],
      ["det A (same as task 1)",CALC(`${DET(A_)} = ${c.w.l2}`)+CALC(`= ${c.w.l3} = <b>${nm(c.det)}</b>`)],
      ["All nine cofactors",`<div class="cofs">${[0,1,2].flatMap(i=>[0,1,2].map(j=>`<p class="calc sm">${Cf(i+1,j+1)} = ${sgn(i,j)>0?"+":"−"}(${in2(minor(A,i,j))}) = ${nm(c.Co[i][j])}</p>`)).join("")}</div>`],
      ["Flip them across the diagonal",wk(`<span class="mu">adj</span>&#8202;${A_} = ${MX(c.adj)}`)+`<p class="small">Row 1 of adj A is C₁₁, C₂₁, C₃₁, and so on.</p>`],
      ["Multiply adj A by (C − B)",wk(`${MX(c.adj,{s:1})}${MX(c.CB,{s:1})} = ${MX(c.P,{s:1})}`)+lines(prodLines(c.adj,c.CB,c.P))],
      ["Divide by det A",wk(`${X_} = ${FR("1",nm(c.det))}${MX(c.P)} = ${MX(c.X)}`)],
      ["Read off the answers",CALC(`${sb(mi("x"),"11")} = <b>${nm(c.X[0][0])}</b>`)+CALC(`sum = ${sumS(c.X.flat())} = <b>${nm(c.S)}</b>`)]
    ])+checkline(`${A_}${X_} = ${MX(mul(A,c.X),{s:1})}, and adding ${B_} gives ${MX(madd(mul(A,c.X),p.B),{s:1})}, which is ${C_} ✓`)+
    finalAns(`${X_} = ${MX(c.X,{s:1})}, &nbsp;${sb(mi("x"),"11")} = ${nm(c.X[0][0])}, &nbsp;sum = ${nm(c.S)}`);},
  sheet:[{name:"3×3 matrix equation",eq:`${X_}${OP("=")}${FR("1",DET(A_))}${OP("·")}<span class="mu">adj</span>&#8202;${A_}${OP("·")}(${C_}${OP("−")}${B_})`,note:"adj A = cofactors flipped across the diagonal. Divide by det A at the very end."}],
  takeEq:()=>`${X_}${OP("=")}${FR("1",DET(A_))}${OP("·")}<span class="mu">adj</span>&#8202;${A_}${OP("·")}(${C_}${OP("−")}${B_})`,
  takeaway:"Same two moves as the 2×2 version: C − B, then A⁻¹ on the left. Build A⁻¹ from all nine cofactors, flipped, and divide by det A last.",
  link:(p,c)=>`${optLine(p,c.S)} The table on the exam is for the sum (part b).`,
  viz:vizSteps("Check the answer: multiply A by your X, row by column, then add B. You should land exactly on C.",p=>{const c=calc6(p);return mulStepper(p.A,c.X,p.B,["A","X","B","C"]);})
};

/* ======================================================================
   Task 7: general solution of 3 equations in 4 unknowns
   ====================================================================== */
function calc7(p){const [q1,q2]=p.E,D=q1[0]*q2[1]-q1[1]*q2[0];
  const col=(u1,u2)=>[u1*q2[1]-q1[1]*u2,q1[0]*u2-u1*q2[0]];   /* numerators of x1, x2 for right-hand sides u1, u2 */
  const a=col(q1[4],q2[4]),b=col(-q1[2],-q2[2]),cc=col(-q1[3],-q2[3]),e3=q1.map((v,k)=>p.al*v+p.be*q2[k]);
  const n1=a[0]+b[0]+cc[0],n2=a[1]+b[1]+cc[1];
  return {D,a,b,c:cc,e3,n1,n2,s1:n1/D,tot:(n1+n2)/D,R1:[q1[4],-q1[2],-q1[3]],R2:[q2[4],-q2[2],-q2[3]]};}
function traps7(p,c){return clean([
  [(c.a[0]+c.a[1]-(c.b[0]+c.c[0]+c.b[1]+c.c[1]))/c.D,"When you move the x₃ and x₄ terms to the right side, their signs flip."],
  [(c.a[0]+c.a[1])/c.D,"That's only a₁ + a₂. The b's and c's (the numbers that go with x₃ and x₄) count too."],
  [c.s1,"That's only x₁'s three numbers. Add a₂ + b₂ + c₂ as well."],
  [c.tot+2,"Add only the six numbers a₁, b₁, c₁, a₂, b₂, c₂. Don't add x₃ and x₄ themselves."],
  [c.n1+c.n2,"Divide by D, the determinant of the x₁, x₂ part."]
],c.tot,0.004,0.001);}
const ABC=(l,i)=>sb(mi(l),i);
const GEN_FORM=`(${ABC("a",1)} + ${ABC("b",1)}${X4[2]} + ${ABC("c",1)}${X4[3]}, &nbsp;${ABC("a",2)} + ${ABC("b",2)}${X4[2]} + ${ABC("c",2)}${X4[3]}, &nbsp;${X4[2]}, &nbsp;${X4[3]})`;
const SIX=`${ABC("a",1)} + ${ABC("b",1)} + ${ABC("c",1)} + ${ABC("a",2)} + ${ABC("b",2)} + ${ABC("c",2)}`;
const comboTxt=p=>`${nm(p.al)} × (equation 1) ${p.be<0?"−":"+"} ${Math.abs(p.be)} × (equation 2)`;
const T7={
  id:"t7",topic:"General solution",
  base:{E:[[1,1,-2,2,-1],[-3,2,-2,1,-2]],al:-2,be:-4,opts:[1.25,1,-1.5,-1,2.25]},
  random:()=>{for(;;){const e=()=>[rnz(-3,3),rnz(-3,3),rnz(-3,3),rnz(-3,3),ri(-5,5)],E=[e(),e()],D=E[0][0]*E[1][1]-E[0][1]*E[1][0];
    if(D===0||Math.abs(D)>9)continue;const al=pick([-4,-3,-2,2,3,4]),be=pick([-4,-3,-2,2,3,4]),e3=E[0].map((v,k)=>al*v+be*E[1][k]);
    if(e3.slice(0,4).some(v=>v===0||Math.abs(v)>20))continue;const p={E,al,be},c=calc7(p);p.opts=makeOpts(c.tot,pmCands(c.tot,traps7(p,c)));return p;}},
  calc:calc7,
  text:(p,G,T)=>{const c=calc7(p);return `The ${T("sys","system")}<span class="dmath">${SYS([{c:p.E[0].slice(0,4),r:p.E[0][4]},{c:p.E[1].slice(0,4),r:p.E[1][4]},{c:c.e3.slice(0,4),r:c.e3[4]}],X4,G,{mark:(i,j)=>i>1?null:j<0?`r${i+1}`:j<2?`p${i+1}${j+1}`:null})}</span>has infinitely many solutions. Its ${T("gen","general solution")} has the form<span class="dmath">${GEN_FORM}</span>where ${X4[2]} and ${X4[3]} can be any numbers. Find ${SIX}.`;},
  after:(p,c,done)=>OPTS(p,c.tot,done),
  terms:{sys:TERMS.sys,gen:TERMS.gen},
  given:p=>{const rows=[];[0,1].forEach(i=>[0,1].forEach(j=>{const v=p.E[i][j],xs=`x${SUBN[j]}`;
      rows.push({k:`p${i+1}${j+1}`,sym:en("p",i+1,j+1),name:`number in front of ${xs} in equation ${i+1}`,unit:"",val:v,why:`Equation ${i+1}, the number that multiplies ${xs}.`,
        look:Math.abs(v)===1?`"${v<0?"−":""}${xs}" with no number in front means ${nm(v)} · ${xs}.`:`The number in front of ${xs} in equation ${i+1}, with its sign.`,gtraps:v<0?[[-v,"Keep the minus sign."]]:[]});}));
    [0,1].forEach(i=>{const v=p.E[i][4];rows.push({k:`r${i+1}`,sym:sb(mi("r"),i+1),name:`right-hand side of equation ${i+1}`,unit:"",val:v,why:"The number after the = sign.",look:`Look after the = sign in equation ${i+1}.`,gtraps:v<0?[[-v,"Keep the minus sign."]]:[]});});
    return rows;},
  find:[{sym:`${ABC("a",1)} + ${ABC("b",1)} + ${ABC("c",1)}`,name:"x₁'s three numbers added",unit:"",why:"Part (a)."},{sym:mi("S"),name:"all six added",unit:"",why:"Part (b). That's the answer."}],
  parts:[Object.assign({id:"s1",label:"(a) a₁ + b₁ + c₁",sym:`${ABC("a",1)} + ${ABC("b",1)} + ${ABC("c",1)}`,unit:"",ans:(p,c)=>c.s1,
      traps:(p,c)=>clean([[(c.a[0]-c.b[0]-c.c[0])/c.D,"When you move the x₃ and x₄ terms to the right side, their signs flip."],[c.a[0]/c.D,"That's only a₁. Add b₁ and c₁ too."],[c.n2/c.D,"That's x₂'s numbers (a₂ + b₂ + c₂). Part (a) is about x₁."],[c.n1,"Divide by D, the determinant of the x₁, x₂ part."]],c.s1,0.004,0.001)},DEC),
    Object.assign({id:"tot",label:"(b) a₁ + b₁ + c₁ + a₂ + b₂ + c₂",sym:mi("S"),unit:"",ans:(p,c)=>c.tot,traps:traps7},DEC)],
  idea:p=>`<p>Three equations, four unknowns. But equation 3 brings nothing new: it's ${comboTxt(p)}. (Check one number to see it.) So really there are 2 equations for 4 unknowns.</p>
    <p>Two equations can pin down two unknowns. So x₃ and x₄ stay free (any numbers), and you solve for x₁ and x₂ in terms of them:</p>
    <ol class="plain"><li>Keep the x₁ and x₂ terms on the left. Move the x₃ and x₄ terms to the right side, flipping their signs.</li><li>Solve those 2 equations for x₁ and x₂ (Cramer's rule with 2×2 determinants is quickest).</li><li>Read off the numbers: a₁ is the plain number in x₁, b₁ goes with x₃, c₁ goes with x₄. Same for x₂.</li></ol>
    <p><b>Shortcut for this question:</b> a₁ + b₁ + c₁ is exactly x₁ when x₃ = 1 and x₄ = 1. So you can put x₃ = 1 and x₄ = 1 into equations 1 and 2, solve that ordinary 2×2 system, and add x₁ + x₂.</p>
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>{const P=(i,j)=>en("p",i,j),r=i=>sb(mi("r"),i),Rr=i=>sb(mi("R"),i);
    return EQ(`${P(1,1)}${X4[0]}${OP("+")}${P(1,2)}${X4[1]}${OP("=")}${Rr(1)}${OP("=")}${r(1)}${OP("−")}${P(1,3)}${X4[2]}${OP("−")}${P(1,4)}${X4[3]}`)+
      EQ(`${P(2,1)}${X4[0]}${OP("+")}${P(2,2)}${X4[1]}${OP("=")}${Rr(2)}${OP("=")}${r(2)}${OP("−")}${P(2,3)}${X4[2]}${OP("−")}${P(2,4)}${X4[3]}`)+
      EQ(`${X4[0]}${OP("=")}${FR(`${Rr(1)}${P(2,2)}${OP("−")}${P(1,2)}${Rr(2)}`,mi("D"))},<span style="margin:0 .7em"></span>${X4[1]}${OP("=")}${FR(`${P(1,1)}${Rr(2)}${OP("−")}${Rr(1)}${P(2,1)}`,mi("D"))},<span style="margin:0 .7em"></span>${mi("D")}${OP("=")}${P(1,1)}${P(2,2)}${OP("−")}${P(1,2)}${P(2,1)}`)+
      legend([[P(1,3),"the number in front of x₃ in equation 1",""],[r(1),"the right-hand side of equation 1",""],[Rr(1),"the right-hand side after moving the x₃ and x₄ terms over",""],[mi("D"),"the 2×2 determinant of the x₁, x₂ numbers",""]],"This is Cramer's rule for two equations: same idea as task 4, with 2×2 determinants.");},
  plug:(p,c)=>{const [q1,q2]=p.E,R1=linT(c.R1[0],[[c.R1[1],X4[2]],[c.R1[2],X4[3]]]),R2=linT(c.R2[0],[[c.R2[1],X4[2]],[c.R2[2],X4[3]]]);
    return EQ(`${linT(0,[[q1[0],X4[0]],[q1[1],X4[1]]])}${OP("=")}${R1}`)+EQ(`${linT(0,[[q2[0],X4[0]],[q2[1],X4[1]]])}${OP("=")}${R2}`)+
      EQ(`${mi("D")}${OP("=")}${pn(q1[0])}·${pn(q2[1])}${OP("−")}${pn(q1[1])}·${pn(q2[0])}`)+
      EQ(`${X4[0]}${OP("=")}${FR(`(${R1})·${pn(q2[1])}${OP("−")}${pn(q1[1])}·(${R2})`,mi("D"))}`)+
      `<p><b>Shortcut:</b> with x₃ = 1 and x₄ = 1, R₁ = ${nm(sum(c.R1))} and R₂ = ${nm(sum(c.R2))}. Then x₁ = a₁ + b₁ + c₁ and x₂ = a₂ + b₂ + c₂.</p>`;},
  solution:(p,c)=>{const [q1,q2]=p.E,D=c.D,R1=linT(c.R1[0],[[c.R1[1],X4[2]],[c.R1[2],X4[3]]]),R2=linT(c.R2[0],[[c.R2[1],X4[2]],[c.R2[2],X4[3]]]);
    const xl=(k)=>linH([[c.a[k],""],[c.b[k],X4[2]],[c.c[k],X4[3]]],D);
    return steps([
      ["Equation 3 adds nothing new",`${comboTxt(p)}:`+lines([0,1,2,3,4].map(k=>`${k<4?`x${SUBN[k]}`:"right side"}: ${nm(p.al)}·${pn(q1[k])} + ${pn(p.be)}·${pn(q2[k])} = ${nm(c.e3[k])}`))+`<p class="small">That's exactly equation 3, so only equations 1 and 2 matter.</p>`],
      ["Move x₃ and x₄ to the right",CALC(`${linT(0,[[q1[0],X4[0]],[q1[1],X4[1]]])} = ${R1}`)+CALC(`${linT(0,[[q2[0],X4[0]],[q2[1],X4[1]]])} = ${R2}`)],
      ["The 2×2 determinant",CALC(`${mi("D")} = ${pn(q1[0])} × ${pn(q2[1])} − ${pn(q1[1])} × ${pn(q2[0])} = <b>${nm(D)}</b>`)],
      ["Solve for x₁",CALC(`${X4[0]} = [(${R1}) × ${pn(q2[1])} − ${pn(q1[1])} × (${R2})] ÷ ${pn(D)}`)+CALC(`= (${linT(c.a[0],[[c.b[0],X4[2]],[c.c[0],X4[3]]])}) ÷ ${pn(D)} = ${xl(0)}`)+`<p class="small">So a₁ = ${frH(c.a[0],D)}, b₁ = ${frH(c.b[0],D)}, c₁ = ${frH(c.c[0],D)}.</p>`],
      ["Solve for x₂",CALC(`${X4[1]} = [${pn(q1[0])} × (${R2}) − (${R1}) × ${pn(q2[0])}] ÷ ${pn(D)}`)+CALC(`= (${linT(c.a[1],[[c.b[1],X4[2]],[c.c[1],X4[3]]])}) ÷ ${pn(D)} = ${xl(1)}`)+`<p class="small">So a₂ = ${frH(c.a[1],D)}, b₂ = ${frH(c.b[1],D)}, c₂ = ${frH(c.c[1],D)}.</p>`],
      ["Add the six numbers",CALC(`${ABC("a",1)} + ${ABC("b",1)} + ${ABC("c",1)} = ${frH(c.n1,D)}${approx(c.n1,D)}`)+CALC(`${SIX} = ${frH(c.n1+c.n2,D)}${approx(c.n1+c.n2,D)}`)]
    ])+checkline(`The shortcut: put x₃ = 1 and x₄ = 1. Then R₁ = ${nm(sum(c.R1))} and R₂ = ${nm(sum(c.R2))}, so x₁ = (${pn(sum(c.R1))}×${pn(q2[1])} − ${pn(q1[1])}×${pn(sum(c.R2))}) ÷ ${pn(D)} = ${frH(c.n1,D)} and x₂ = (${pn(q1[0])}×${pn(sum(c.R2))} − ${pn(sum(c.R1))}×${pn(q2[0])}) ÷ ${pn(D)} = ${frH(c.n2,D)}. Together: ${frH(c.n1+c.n2,D)} ✓`)+
    finalAns(`${ABC("a",1)} + ${ABC("b",1)} + ${ABC("c",1)} = ${frH(c.n1,D)}${approx(c.n1,D)}, &nbsp;${mi("S")} = ${frH(c.n1+c.n2,D)}${approx(c.n1+c.n2,D)}`);},
  sheet:[{name:"Two equations, two unknowns",eq:`${X4[0]}${OP("=")}${FR(`${sb(mi("R"),1)}${en("p",2,2)}${OP("−")}${en("p",1,2)}${sb(mi("R"),2)}`,mi("D"))},${OP("")}${X4[1]}${OP("=")}${FR(`${en("p",1,1)}${sb(mi("R"),2)}${OP("−")}${sb(mi("R"),1)}${en("p",2,1)}`,mi("D"))}`,note:"D = p₁₁p₂₂ − p₁₂p₂₁. R = right side after moving x₃ and x₄ over (signs flip)."},
    {name:"Sum shortcut",eq:`${ABC("a",1)}${OP("+")}${ABC("b",1)}${OP("+")}${ABC("c",1)}${OP("=")}${X4[0]}${OP("")}(${X4[2]}${OP("=")}${X4[3]}${OP("=")}1)`,note:"Put x₃ = x₄ = 1 and solve once."}],
  takeEq:()=>`${ABC("a",1)}${OP("+")}${ABC("b",1)}${OP("+")}${ABC("c",1)}${OP("=")}${X4[0]}${OP("")}at${OP("")}${X4[2]}${OP("=")}${X4[3]}${OP("=")}1`,
  takeaway:"Equation 3 is a mix of the first two, so drop it. Move x₃ and x₄ to the right (signs flip) and solve the 2×2 system. For the sum, just put x₃ = x₄ = 1.",
  link:(p,c)=>`${optLine(p,c.tot)} The table on the exam is for the sum of all six (part b).`,
  viz:{
    html:()=>`<p class="sec-note">Pick any x₃ and x₄. The general solution gives x₁ and x₂, and all three equations still hold. Every choice is a different solution.</p>
      <div class="viz-box"><label class="viz-l" for="g3">x₃ = <output id="g3o">1</output></label><input type="range" id="g3" min="-5" max="5" step="0.5" value="1">
      <label class="viz-l" for="g4">x₄ = <output id="g4o">1</output></label><input type="range" id="g4" min="-5" max="5" step="0.5" value="1"><div id="g-out" class="viz-read" style="display:flex;flex-direction:column;gap:4px"></div></div>`,
    setup:(p,c,ctx)=>{const s3=ctx.$("#g3"),s4=ctx.$("#g4"),out=ctx.$("#g-out"),rows=[p.E[0],p.E[1],c.e3];
      const upd=()=>{const x3=+s3.value,x4=+s4.value,x1=(c.a[0]+c.b[0]*x3+c.c[0]*x4)/c.D,x2=(c.a[1]+c.b[1]*x3+c.c[1]*x4)/c.D,xs=[x1,x2,x3,x4];
        ctx.$("#g3o").textContent=nm(x3);ctx.$("#g4o").textContent=nm(x4);
        out.innerHTML=`<p>(x₁, x₂, x₃, x₄) = (<b>${nm(x1)}</b>, <b>${nm(x2)}</b>, ${nm(x3)}, ${nm(x4)})</p>`+
          rows.map((e,i)=>`<p class="small">Equation ${i+1}: ${e.slice(0,4).map((v,k)=>`${pn(v)}·${pn(xs[k])}`).join(" + ")} = <span class="ok-t">${nm(sum(e.slice(0,4).map((v,k)=>v*xs[k])))} ✓</span></p>`).join("")+
          (x3===1&&x4===1?`<p>At x₃ = x₄ = 1: x₁ + x₂ = <b>${nm(x1+x2)}</b>, the answer to this question.</p>`:"");};
      s3.addEventListener("input",upd);s4.addEventListener("input",upd);upd();}
  }
};

/* ======================================================================
   Task 8: A·X⁻¹·B⁻¹ = C
   ====================================================================== */
function calc8(p){const dB=det2(p.B),dC=det2(p.C),aB=adj2(p.B),aC=adj2(p.C),Q=mul(aC,p.A),P=mul(aB,Q),den=dB*dC;return {dB,dC,aB,aC,Q,P,den,S:msum(P)/den};}
function traps8(p,c){const dA=det2(p.A),aA=adj2(p.A);return clean([
  [msum(mul(mul(aA,p.C),p.B))/dA,"That's X⁻¹ = A⁻¹CB. You still need to invert it: X = B⁻¹C⁻¹A."],
  [msum(mul(mul(p.A,c.aC),c.aB))/c.den,"Inverting a product flips the order: (A⁻¹CB)⁻¹ = B⁻¹C⁻¹A, not AC⁻¹B⁻¹."],
  [msum(mul(mul(c.aC,c.aB),p.A))/c.den,"Nearly: B⁻¹ comes first. X = B⁻¹C⁻¹A."],
  [msum(c.P)/c.dC,"You forgot to divide by det B (the 1/det B in front of B⁻¹)."],
  [msum(c.P)/c.dB,"You forgot to divide by det C (the 1/det C in front of C⁻¹)."],
  [msum(c.P),"Divide by det B × det C at the end."]
],c.S,0.004,0.001);}
const T8_EQ=`${A_}${INV(X_)}${INV(B_)}${OP("=")}${C_}${IMPLIES}${X_}${OP("=")}${INV(B_)}${INV(C_)}${A_}`;
const T8={
  id:"t8",topic:"Equation with inverses",
  base:{A:[[-4,4],[-8,-12]],B:[[-1,2],[1,2]],C:[[2,1],[-3,3]],opts:[-4.889,-4.389,-3.889,-3.389,-2.889]},
  random:()=>{const ev=()=>pick([-12,-8,-6,-4,-2,2,4,6,8,12]),sv=()=>rnz(-3,3);
    for(;;){const A=[[ev(),ev()],[ev(),ev()]],B=[[sv(),sv()],[sv(),sv()]],C=[[sv(),sv()],[sv(),sv()]];
      if(!det2(A)||!det2(B)||!det2(C)||Math.abs(det2(B)*det2(C))>36)continue;
      const p={A,B,C},c=calc8(p),k=ri(0,4);p.opts=[0,1,2,3,4].map(i=>r3(c.S+(i-k)*0.5));return p;}},
  calc:calc8,
  text:(p,G,T)=>`<span class="dmath">${A_} = ${MX(p.A,{cell:markCells([[1,1]],G,"a")})}, &nbsp;${B_} = ${MX(p.B,{cell:markCells([[1,2]],G,"b")})}, &nbsp;${C_} = ${MX(p.C,{cell:markCells([[2,1],[2,2]],G,"c")})}</span>The unknown ${T("X","matrix X")} satisfies ${A_}${INV(X_)}${INV(B_)} = ${C_}. Find the sum of all the elements of ${X_}.`,
  after:(p,c,done)=>OPTS(p,c.S,done,false),
  terms:{X:TERMS.X},
  given:p=>[gEntry(p.A,1,1,{of:"A",why:"Top-left of A."}),gEntry(p.B,1,2,{l:"b",of:"B",why:"Top-right of B."}),gEntry(p.C,2,1,{l:"c",of:"C",why:"Bottom-left of C."}),gEntry(p.C,2,2,{l:"c",of:"C",why:"Bottom-right of C."})],
  find:[{sym:mi("S"),name:"the sum of all elements of X",unit:"",why:"One number. That's the answer."}],
  parts:[Object.assign({id:"s",label:"Sum of all the elements of X",sym:mi("S"),unit:"",ans:(p,c)=>c.S,traps:traps8},DEC)],
  idea:()=>`<p>Get X on its own one matrix at a time. Two rules:</p>
    <ul class="plain"><li>To remove a matrix, multiply both sides by its inverse <b>on the same side</b> it sits (left stays left, right stays right). To remove an inverse like B⁻¹, multiply by B itself, because B⁻¹B = I, and I changes nothing.</li>
    <li>Inverting a product <b>reverses</b> the order: (PQR)⁻¹ = R⁻¹Q⁻¹P⁻¹.</li></ul>
    <ol class="plain"><li>B⁻¹ is on the right: multiply both sides by B on the right → A X⁻¹ = C B.</li><li>A is on the left: multiply by A⁻¹ on the left → X⁻¹ = A⁻¹ C B.</li><li>Invert both sides → X = B⁻¹ C⁻¹ A.</li></ol>
    <p>Then it's two 2×2 inverses and two multiplications.</p>
    <p class="small">Try it now. The next hint gives you the formula.</p>`,
  formula:()=>EQ(T8_EQ)+EQ(INV2_EQ)+EQ(MUL2_EQ)+legend([[INV(B_),"the inverse of B",""]],"Keep the two 1/det numbers in front and multiply whole numbers first: X = 1/(det B · det C) × (B's swapped matrix) × (C's swapped matrix) × A."),
  plug:p=>{const B=p.B,C=p.C;
    return EQ(T8_EQ)+EQ(`${INV(B_)}${OP("=")}${FR("1",`${pn(B[0][0])}·${pn(B[1][1])} − ${pn(B[0][1])}·${pn(B[1][0])}`)}${MX(adj2(B))}`)+
      EQ(`${INV(C_)}${OP("=")}${FR("1",`${pn(C[0][0])}·${pn(C[1][1])} − ${pn(C[0][1])}·${pn(C[1][0])}`)}${MX(adj2(C))}`)+
      EQ(`${X_}${OP("=")}${INV(B_)}${OP("·")}${INV(C_)}${OP("·")}${MX(p.A)}`)+
      `<p class="tip"><b>Tip:</b> multiply C⁻¹ by A first, then put B⁻¹ in front of that.</p>`;},
  solution:(p,c)=>steps([
      ["Get X on its own",`<div class="alg"><span>${A_}${INV(X_)}${INV(B_)} = ${C_}</span><span>× ${B_} on the right: ${A_}${INV(X_)} = ${C_}${B_}</span><span>× ${INV(A_)} on the left: ${INV(X_)} = ${INV(A_)}${C_}${B_}</span><span>invert, order flips: ${X_} = ${INV(B_)}${INV(C_)}${A_}</span></div>`],
      ["Inverse of B",CALC(`${DET(B_)} = ${pn(p.B[0][0])} × ${pn(p.B[1][1])} − ${pn(p.B[0][1])} × ${pn(p.B[1][0])} = ${nm(c.dB)}`)+wk(`${INV(B_)} = ${FR("1",nm(c.dB))}${MX(c.aB)}`)],
      ["Inverse of C",CALC(`${DET(C_)} = ${pn(p.C[0][0])} × ${pn(p.C[1][1])} − ${pn(p.C[0][1])} × ${pn(p.C[1][0])} = ${nm(c.dC)}`)+wk(`${INV(C_)} = ${FR("1",nm(c.dC))}${MX(c.aC)}`)],
      ["Multiply C's part by A",wk(`${MX(c.aC)}${MX(p.A)} = ${MX(c.Q)}`)+lines(prodLines(c.aC,p.A,c.Q))],
      ["Put B's part in front",wk(`${MX(c.aB)}${MX(c.Q)} = ${MX(c.P)}`)+lines(prodLines(c.aB,c.Q,c.P))],
      ["Divide by det B · det C and add up",wk(`${X_} = ${FR("1",`${pn(c.dB)}·${pn(c.dC)}`)}${MX(c.P)}`)+CALC(`sum = (${sumS(c.P.flat())}) ÷ ${pn(c.den)} = ${nm(msum(c.P))} ÷ ${pn(c.den)} = ${frH(msum(c.P),c.den)}${approx(msum(c.P),c.den)}`)]
    ])+checkline((()=>{const X=c.P.map(r=>r.map(v=>v/c.den)),dX=det2(X),Xi=adj2(X).map(r=>r.map(v=>v/dX)),Bi=c.aB.map(r=>r.map(v=>v/c.dB)),L=mul(mul(p.A,Xi),Bi);
      return `Put X back in: ${A_}${INV(X_)}${INV(B_)} = ${MX(L,{s:1})}, which is ${C_} ✓`;})())+
    finalAns(`sum = ${frH(msum(c.P),c.den)}${approx(msum(c.P),c.den)}`),
  sheet:[{name:"Undoing inverses",eq:T8_EQ,note:"Multiply on the same side. Inverting a product reverses the order."},{name:"2×2 inverse",eq:INV2_EQ,note:"Swap the diagonal, change the signs of the other two, divide by the determinant."}],
  takeEq:()=>T8_EQ,
  takeaway:"Peel matrices off on the side where they sit (B on the right, A⁻¹ on the left), then invert: the order flips, X = B⁻¹C⁻¹A.",
  link:(p,c)=>`${optLine(p,c.S)} This task has no NP option on the sample sheet, so the answer is always in the table.`,
  viz:vizSteps("How X gets peeled out, one matrix at a time.",(p,c)=>{const a=`<span class="tA">A</span>`,b=`<span class="tB">B</span>`,cc=`<span class="tC">C</span>`,xi=`X<sup>−1</sup>`,s=t=>`<span class="alg" style="font-size:1.35rem">${t}</span>`;return [
    {html:s(`${a}·${xi}·${b}<sup>−1</sup> = ${cc}`),note:"Start: X is stuck between A on the left and B⁻¹ on the right."},
    {html:s(`${a}·${xi}·${b}<sup>−1</sup>·${b} = ${cc}·${b}<br>${a}·${xi} = ${cc}·${b}`),note:"Multiply both sides by B <b>on the right</b>. B⁻¹·B = I, which does nothing, so B⁻¹ disappears from the left side."},
    {html:s(`${a}<sup>−1</sup>·${a}·${xi} = ${a}<sup>−1</sup>·${cc}·${b}<br>${xi} = ${a}<sup>−1</sup>·${cc}·${b}`),note:"Multiply both sides by A⁻¹ <b>on the left</b>. A⁻¹·A = I, so A disappears."},
    {html:s(`X = (${a}<sup>−1</sup>·${cc}·${b})<sup>−1</sup> = ${b}<sup>−1</sup>·${cc}<sup>−1</sup>·${a}`),note:"Invert both sides. Inverting a product reverses the order, and the inverse of A⁻¹ is A again."},
    {html:`${X_}<span>=</span><span>${FR("1",nm(c.den))}</span>${MX(c.P)}`,note:`With the numbers: the elements add up to ${nm(msum(c.P))} ÷ ${pn(c.den)} = <b>${frH(msum(c.P),c.den)}${approx(msum(c.P),c.den)}</b>.`}
  ];})
};

/* Task 2 has two versions the student picks between: the sample sheet's (with zeros) and a full expansion. */
const QUESTIONS=[T1,{id:"t2",choose:"Version",pool:[T2,T2F]},T3,T4,T5,T6,T7,T8];
window.__MATH_QS=[T1,T2,T2F,T3,T4,T5,T6,T7,T8];  /* used by the self-check script */
HL.start({
  id:"math-midterm-1",
  title:"Math Midterm 1 Practice",
  eyebrow:"Math exam practice · 8 tasks",
  random:true,
  newAll:true,
  themeToggle:true,
  noun:"tasks",
  gsym:false,
  rungs:[
    ["Write down what you know","Name the numbers you'll use"],
    ["Which idea to use","The method in plain words, no formula yet"],
    ["The formula","The formula, with every symbol explained"],
    ["Plug in the numbers","The formula with your numbers already in it"],
    ["Full solution","Every step worked out, with a check"]
  ],
  givenIntro:"Every matrix question starts the same way: find the numbers you'll use and name them. a₂₃ means the number in row 2, column 3. Rows go across (counted from the top) and columns go down (counted from the left). The numbers you need are now highlighted in the question. Type each one in the box next to its name. When you click a box, its number lights up.",
  calcNote:"Type a whole number, a decimal (like −0.383) or a fraction (like −102/266). You can also type a calculation, like <code>5*(-21)-(-5)*(-35)</code>.",
  linkLabel:"On the exam",
  onRenewAll:on=>{SHARED=on?{A:randA()}:null;},
  questions:QUESTIONS
});
})();
