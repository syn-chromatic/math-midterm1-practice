/* Midterm practice engine (the physics and maths pages share it)
   A page loads engine.css + engine.js, then calls HL.start({id, setName, lede, next, questions:[...]}).
   Helpers for writing questions are on window.HL. HL.selfTest() checks every question and variant. */
(function(){
"use strict";
const $=(s,el)=>(el||document).querySelector(s);
const $$=(s,el)=>Array.from((el||document).querySelectorAll(s));
const pick=a=>a[Math.floor(Math.random()*a.length)];
const reduceMotion=!!(window.matchMedia&&window.matchMedia("(prefers-reduced-motion: reduce)").matches);
const esc=s=>String(s).replace(/[&<>"]/g,ch=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[ch]));
const near=(x,y,tol)=>Number.isFinite(x)&&Math.abs(x-y)<=Math.abs(y)*(tol==null?0.02:tol)+1e-9;
const cap=s=>s.charAt(0).toUpperCase()+s.slice(1);
function fmt(x){
  if(!Number.isFinite(x)) return "?";
  const ax=Math.abs(x);
  if(ax===0) return "0";
  if(ax>=1000) return String(Math.round(x)).replace(/\B(?=(\d{3})+(?!\d))/g," ");
  return String(Number(x.toPrecision(3)));
}

/* ---------- math typesetting helpers ---------- */
const mi=s=>`<i class="mi">${s}</i>`;
const up=s=>`<span class="mu">${s}</span>`;
const sb=(b,s)=>`${b}<sub>${s}</sub>`;
const ssp=(b,s,p)=>`${b}<span class="ss"><sup>${p}</sup><sub>${s}</sub></span>`;
const OP=s=>`<span class="op">${s}</span>`;
const FR=(a,b)=>`<span class="fr"><span class="fr-n">${a}</span><span class="fr-d">${b}</span></span>`;
const SQ=(x,tall)=>`<span class="sq${tall?" tall":""}"><span class="sq-s">√</span><span class="sq-x">${x}</span></span>`;
const EQ=h=>`<div class="eq-wrap"><div class="eq">${h}</div></div>`;
const CALC=h=>`<div class="calc">${h}</div>`;
const HALF=FR("1","2");
const sq2=x=>`${x}<sup>2</sup>`;
const neg=x=>String(x).replace("-","−");
const IMPLIES=`<span class="op" style="margin:0 .7em">⟹</span>`;
const AND=`<span class="op" style="margin:0 .9em">and</span>`;
const PAREN=x=>`<span class="paren">(</span>${x}<span class="paren">)</span>`;
const PI=up("π"), OMEGA=mi("ω");
const V0=sb(mi("v"),"0"), VI=sb(mi("v"),"i"), VF=sb(mi("v"),"f");
const KE=up("KE"), KEI=sb(up("KE"),"i"), KEF=sb(up("KE"),"f"), DKE=up("Δ")+up("KE");

const legend=(rows,note)=>`<div class="legend">${rows.map(r=>`<div class="lg-sym">${r[0]}</div><div>${r[1]}</div><div class="lg-unit">${r[2]}</div>`).join("")}</div>${note?`<p class="note">${note}</p>`:""}`;
const steps=list=>`<ol class="steps">${list.map(([t,b])=>`<li><p class="st-t">${t}</p><div class="st-b">${b}</div></li>`).join("")}</ol>`;
const checkline=h=>`<p class="checkline"><span class="tk-label">Check</span><br>${h}</p>`;
const finalAns=h=>`<div class="final"><span class="tk-label">Answer</span><div class="calc big">${h}</div></div>`;
const watch=h=>`<div class="watch"><b>Common mistake.</b> ${h}</div>`;
const calcTip=(e,more)=>`<p class="tip"><b>Tip:</b> you can type <code>${e}</code> straight into the answer box. It works out the result for you.${more||""}</p>`;

const DEFAULT_RUNGS=[
  ["Write down what you know","List the numbers from the question, with symbols and units"],
  ["Which idea to use","The physics in plain words, no formula yet"],
  ["The formula","The equation, with every symbol explained"],
  ["Plug in the numbers","The formula with your numbers already in it"],
  ["Full solution","Every step worked out, with a check"]
];
let RUNGS=DEFAULT_RUNGS;
const val2=(x,p,c)=>typeof x==="function"?x(p,c):x;

/* ---------- number parsing ---------- */
function plainCandidates(s){
  s=s.trim();let sign="";
  if(/^[+-]/.test(s)){sign=s[0];s=s.slice(1);}
  s=s.replace(/\s+/g,"");
  const out=[];
  if(s.includes(".")&&s.includes(",")) out.push(s.replace(/,/g,""));
  else if(s.includes(",")){
    if(/^[1-9]\d{0,2}(,\d{3})+$/.test(s)) out.push(s.replace(/,/g,""));
    if((s.match(/,/g)||[]).length===1) out.push(s.replace(",","."));
  } else out.push(s);
  return out.map(x=>Number(sign+x)).filter(Number.isFinite);
}
function evaluate(src){
  let s=String(src).trim();
  if(!s) return null;
  s=s.replace(/[×·∙⋅]/g,"*").replace(/÷/g,"/").replace(/[−–]/g,"-").replace(/π/g,"pi").replace(/√/g,"sqrt").replace(/[⁻⁺]?[⁰¹²³⁴⁵⁶⁷⁸⁹]+/g,m=>"^("+m.replace(/[⁻⁺⁰¹²³⁴⁵⁶⁷⁸⁹]/g,ch=>({"⁻":"-","⁺":"+","⁰":"0","¹":"1","²":"2","³":"3","⁴":"4","⁵":"5","⁶":"6","⁷":"7","⁸":"8","⁹":"9"})[ch])+")").replace(/,/g,".").toLowerCase().replace(/\s+/g,"");
  const toks=[];let i=0;
  while(i<s.length){
    const rest=s.slice(i);let m;
    if((m=rest.match(/^(\d+\.?\d*|\.\d+)(e[+-]?\d+)?/))){toks.push({t:"n",v:parseFloat(m[0])});i+=m[0].length;continue;}
    if((m=rest.match(/^(sqrt|pi|log10|log|lg|ln|exp|e|x)/))){toks.push(m[1]==="x"?{t:"o",v:"*"}:{t:"id",v:m[1]});i+=m[0].length;continue;}
    if("+-*/^()".includes(rest[0])){toks.push({t:"o",v:rest[0]});i++;continue;}
    return null;
  }
  let k=0;
  const peek=()=>toks[k];
  const eat=v=>{if(toks[k]&&toks[k].t==="o"&&toks[k].v===v){k++;return true;}return false;};
  function expr(){let v=term();while(peek()&&peek().t==="o"&&(peek().v==="+"||peek().v==="-")){const o=toks[k++].v;const r=term();v=o==="+"?v+r:v-r;}return v;}
  function term(){let v=unary();for(;;){const t=peek();if(!t)break;
      if(t.t==="o"&&(t.v==="*"||t.v==="/")){k++;const r=unary();v=t.v==="*"?v*r:v/r;}
      else if(t.t==="n"||t.t==="id"||(t.t==="o"&&t.v==="(")){v*=power();}
      else break;}
    return v;}
  function unary(){if(eat("-"))return -unary();if(eat("+"))return unary();return power();}
  function power(){const b=primary();if(eat("^"))return Math.pow(b,unary());return b;}
  function primary(){const t=toks[k++];if(!t)throw 0;
    if(t.t==="n")return t.v;
    if(t.t==="id"){if(t.v==="pi")return Math.PI;if(t.v==="sqrt")return Math.sqrt(power());if(t.v==="ln")return Math.log(power());if(t.v==="exp")return Math.exp(power());if(t.v==="e")return Math.E;if(t.v==="log"||t.v==="log10"||t.v==="lg")return Math.log10(power());}
    if(t.t==="o"&&t.v==="("){const v=expr();if(!eat(")"))throw 0;return v;}
    throw 0;}
  try{const v=expr();if(k!==toks.length)return null;return Number.isFinite(v)?v:null;}catch(e){return null;}
}
const UNIT_RE=/\s*(degrees|degree|deg|°|kg·m²\/s|kg\*m\^2\/s|kgm\^2\/s|kgm²\/s|w\/m2|w\/m\^2|kg·m²|kg\*m\^2|kgm\^2|kg m\^2|kgm²|kg·m\/s|kg\*m\/s|kgm\/s|m\/s²|m\/s\^2|m\/s2|m\/s|rad\/s²|rad\/s\^2|rad\/s|rad|n·m|n\*m|n·s|n\*s|ns|nm|kj|khz|hz|kg|n\/m|w\/m²|db|cm|j|n|s|m|w)\s*$/i;
const isPlain=s=>/^[+-]?[\d\s.,]+$/.test(s.trim());
function candidates(raw){
  const s=String(raw||"").trim().replace(UNIT_RE,"");
  if(!s) return [];
  if(isPlain(s)) return plainCandidates(s);
  const v=evaluate(s);
  return v==null?[]:[v];
}
function previewText(raw){
  const s=String(raw||"").trim().replace(UNIT_RE,"");
  if(!s||isPlain(s)) return "";
  const v=evaluate(s);
  return v==null?"Can't read that yet. Use numbers with + − * / ^ ( ), sqrt( ), log( ), ln( ), e and pi.":`= ${fmt(v)}`;
}

/* ---------- animation loops (stopped on every re-render) ---------- */
let loops=[];
function makeLoop(fn){
  const L={raf:0,last:0,alive:true};
  const tick=ts=>{if(!L.alive)return;const dt=L.last?Math.min(0.05,(ts-L.last)/1000):0;L.last=ts;try{fn(dt);}catch(e){L.alive=false;return;}L.raf=requestAnimationFrame(tick);};
  L.raf=requestAnimationFrame(tick);loops.push(L);return L;
}
let cleanups=[];
function stopLoops(){loops.forEach(L=>{L.alive=false;cancelAnimationFrame(L.raf);});loops=[];cleanups.forEach(f=>{try{f();}catch(e){}});cleanups=[];}

/* ---------- "See it" presets ---------- */
/* Slider with bars. cfgFn(p,c) returns {note,label,unit,min,max,step,value,bars:[{label,segs:[{cls,name,frac:(x)=>0..1}]}],read:(x)=>html} */
function vizSlider(cfgFn){
  return {
    html:(p,c)=>{const o=cfgFn(p,c);
      return `${o.note?`<p class="sec-note">${o.note}</p>`:""}<div class="viz-box">
        <label class="viz-l" for="vz-s">${o.label}: <output id="vz-so">${fmt(o.value)}</output> ${o.unit||""}</label>
        <input type="range" id="vz-s" min="${o.min}" max="${o.max}" step="${o.step}" value="${o.value}">
        ${(o.bars||[]).map((b,i)=>`${b.label?`<span class="label">${b.label}</span>`:""}<div class="bar stack">${b.segs.map((sg,j)=>`<div class="seg ${sg.cls||"seg-ke"}" id="vz-b${i}-${j}"></div>`).join("")}</div>${b.segs.some(sg=>sg.name)?`<div class="legend-row">${b.segs.map(sg=>`<span><i class="sw ${(sg.cls||"seg-ke").replace("seg-","sw-")}"></i>${sg.name||""}</span>`).join("")}</div>`:""}`).join("")}
        <p class="viz-read" id="vz-read"></p></div>`;},
    setup:(p,c,ctx)=>{const o=cfgFn(p,c),r=ctx.$("#vz-s");if(!r)return;
      const upd=()=>{const x=+r.value;ctx.$("#vz-so").textContent=fmt(x);
        (o.bars||[]).forEach((b,i)=>b.segs.forEach((sg,j)=>{const f=Math.max(0,Math.min(1,+sg.frac(x)||0));const el=ctx.$(`#vz-b${i}-${j}`);if(el)el.style.width=(f*100)+"%";}));
        if(o.read)ctx.$("#vz-read").innerHTML=o.read(x);};
      r.addEventListener("input",upd);upd();}
  };
}
/* Block on a spring. infoFn(p,c) returns {T,label,note,mark?(x/A, 0..1),markLabel?} */
function springPath(x1,x2,y){
  const lead=10,n=14,w=x2-x1-2*lead;
  let d=`M${x1},${y} L${x1+lead},${y}`;
  for(let i=0;i<n;i++){d+=` L${(x1+lead+w*(i+0.5)/n).toFixed(1)},${y+(i%2?11:-11)}`;}
  return d+` L${x2-lead},${y} L${x2},${y}`;
}
function vizSpring(infoFn){
  return {
    html:(p,c)=>{const info=infoFn(p,c),mx=info.mark!=null?(218+info.mark*60).toFixed(1):null;
      return `<p class="sec-note">${info.note}</p>
      <div class="viz-box">
        <svg class="spring-svg" viewBox="0 0 400 100" role="img" aria-label="A block on a spring bouncing back and forth">
          <line class="wall" x1="12" y1="12" x2="12" y2="86"/>
          <line class="floor" x1="12" y1="84" x2="392" y2="84"/>
          <line class="turn" x1="158" y1="18" x2="158" y2="84"/><line class="turn" x1="278" y1="18" x2="278" y2="84"/>
          <line class="eqline" x1="218" y1="14" x2="218" y2="84"/>
          <text class="mark-t" x="158" y="97" text-anchor="middle">−A</text><text class="mark-t" x="218" y="97" text-anchor="middle">0</text><text class="mark-t" x="278" y="97" text-anchor="middle">A</text>
          ${mx?`<line class="markline" x1="${mx}" y1="16" x2="${mx}" y2="84"/><text class="mark-t hot" x="${mx}" y="11" text-anchor="middle">${info.markLabel||""}</text>`:""}
          <path id="sp-path" class="spring" d=""/>
          <rect id="sp-block" class="block" x="190" y="40" width="56" height="42" rx="4"/>
          <text id="sp-text" class="block-t" x="218" y="66" text-anchor="middle">${info.label}</text>
        </svg>
        <div class="btn-row"><button class="btn" id="sp-play">Pause</button><button class="btn btn-ghost" id="sp-slow">Slow motion</button></div>
        <p class="viz-read" id="sp-read"></p>
      </div>`;},
    setup:(p,c,ctx)=>{const info=infoFn(p,c),path=ctx.$("#sp-path");if(!path)return;
      const block=ctx.$("#sp-block"),txt=ctx.$("#sp-text"),read=ctx.$("#sp-read"),bp=ctx.$("#sp-play"),bs=ctx.$("#sp-slow");
      const st={playing:!ctx.reduceMotion,slow:false,t:0},A=60,eq=190;
      const draw=()=>{const x=eq+A*Math.cos(2*Math.PI*st.t/info.T);block.setAttribute("x",x.toFixed(1));txt.setAttribute("x",(x+28).toFixed(1));path.setAttribute("d",springPath(12,x,61));
        read.innerHTML=`Full back-and-forths so far: <b>${Math.floor(st.t/info.T)}</b> · time: ${st.t.toFixed(1)} s${st.slow?" (slow motion, 10× slower)":""}`;};
      bp.textContent=st.playing?"Pause":"Play";
      bp.addEventListener("click",()=>{st.playing=!st.playing;bp.textContent=st.playing?"Pause":"Play";});
      bs.addEventListener("click",()=>{st.slow=!st.slow;bs.textContent=st.slow?"Real speed":"Slow motion";draw();});
      draw();ctx.loop(dt=>{if(st.playing){st.t+=dt*(st.slow?0.1:1);draw();}});}
  };
}

/* ---------- engine state ---------- */
let CFG={},QS=[],SLOTS=[],VIEW={},state=null,STORE="physics-hint-ladder";
/* A slot with a pool shows one of several versions (e.g. easier/harder); state.qs[id].which says which. */
function viewOf(sl){const s=state.qs[sl.id],w=(s&&s.which)||0,key=sl.id+"#"+w;
  if(!VIEW[key])VIEW[key]=Object.assign({},sl.pool[w],{id:sl.id,set:sl.set!=null?sl.set:sl.pool[w].set});return VIEW[key];}
function resolve(){QS=SLOTS.map(sl=>sl.pool?viewOf(sl):sl);}
const setLabel=n=>((CFG.sets||[]).find(x=>x.n===n)||{}).label||`Set ${n}`;
const allDefs=()=>SLOTS.flatMap(sl=>sl.pool?sl.pool.map(d=>Object.assign({},d,{id:sl.id+"/"+(d.level||"v")})):[sl]);
const val=(x,p)=>typeof x==="function"?x(p):x;
function freshQ(q,params){return {params:params||Object.assign({},q.base),hints:0,folded:{},armed:false,gv:{},gcheck:{},gmsg:{},grevealed:false,inputs:{},solved:{},fb:{},term:null,usedSolution:false,roundDone:false,solvedWith:null,best:null,wins:0};}
function save(){try{localStorage.setItem(STORE,JSON.stringify(state));}catch(e){}}
const allSolved=q=>q.parts.every(pt=>state.qs[q.id].solved[pt.id]);

/* ---------- rendering ---------- */
function sheetEntries(){
  const out=[];
  QS.forEach(q=>{const s=state.qs[q.id];if(s.hints>=3||allSolved(q)||s.wins>0)q.sheet.forEach(e=>out.push(Object.assign({topic:q.topic},e)));});
  return out;
}
const statusOf=q=>{const s=state.qs[q.id];return allSolved(q)?"Solved":s.hints?`${s.hints} hint${s.hints>1?"s":""} open`:"Not started";};
function navHTML(){
  const chips=QS.map((q,i)=>{
    const done=allSolved(q),status=statusOf(q);
    return `<button class="chip${i===state.cur?" is-cur":""}${done?" is-done":""}" data-act="go" data-i="${i}"${i===state.cur?' aria-current="step"':""}><span class="chip-n">${done?"✓":i+1}</span><span class="chip-t"><span class="chip-topic">${q.topic}</span><span class="chip-s">${status}</span></span></button>`;
  }).join("");
  const n=QS.filter(allSolved).length;
  const results=`<button class="chip${state.cur===QS.length?" is-cur":""}" data-act="go" data-i="${QS.length}"><span class="chip-n">Σ</span><span class="chip-t"><span class="chip-topic">Results</span><span class="chip-s">${n} of ${QS.length} solved</span></span></button>`;
  if(CFG.sets){
    const one=(q,i)=>chips.split("</button>")[i]+"</button>";
    return CFG.sets.map(st=>`<div class="set-row"><span class="label">${st.label||`Set ${st.n}`}</span><div class="chips">${QS.map((q,i)=>q.set===st.n?one(q,i):"").join("")}</div></div>`).join("")+`<div class="set-row"><span class="label">Overall</span><div class="chips">${results}</div></div>`;
  }
  return chips+results;
}
function sheetHTML(){
  const items=sheetEntries();
  if(!items.length) return `<div class="sheet" id="sheet"><p class="small">Formulas appear here once you open hint 3 on a question, or solve it.</p></div>`;
  return `<div class="sheet" id="sheet">${items.map(e=>`<div class="sheet-item"><span class="label">${e.topic} · ${e.name}</span>${EQ(e.eq)}<p class="small">${e.note||""}</p></div>`).join("")}</div>`;
}
/* Light / dark switch. With no choice saved, the page follows the device setting. */
const THEME_KEY="hl-theme";
const isDark=()=>{const t=document.documentElement.getAttribute("data-theme");return t?t==="dark":!!(window.matchMedia&&window.matchMedia("(prefers-color-scheme: dark)").matches);};
const SUN='<svg viewBox="0 0 24 24" width="16" height="16" aria-hidden="true"><circle cx="12" cy="12" r="4.2"/><path d="M12 2.5v2.2M12 19.3v2.2M2.5 12h2.2M19.3 12h2.2M5.3 5.3l1.6 1.6M17.1 17.1l1.6 1.6M5.3 18.7l1.6-1.6M17.1 6.9l1.6-1.6"/></svg>';
const MOON='<svg viewBox="0 0 24 24" width="16" height="16" aria-hidden="true"><path d="M20 14.5A8.5 8.5 0 0 1 9.5 4a8.5 8.5 0 1 0 10.5 10.5z"/></svg>';
function themeBtnHTML(){const d=isDark();return `<button class="btn theme-btn" data-act="theme" aria-label="Switch to ${d?"light":"dark"} mode">${d?SUN:MOON}<span>${d?"Light mode":"Dark mode"}</span></button>`;}
function headHTML(){
  return `<header class="top">
    <div class="top-row"><p class="eyebrow">${CFG.eyebrow||`Physics exam practice${CFG.setName?` · ${CFG.setName}`:""} · ${QS.length} questions`}</p>${CFG.themeToggle?themeBtnHTML():""}</div>
    <h1>${CFG.title||"Physics Midterm 1 Practice"}${CFG.setName?` <span class="h1-set">${CFG.setName}</span>`:""}</h1>
  </header>`;
}
/* "New numbers" in the side panel: always asks first, and explains that it changes every question */
const unfinished=()=>QS.some(q=>{const s=state.qs[q.id];if(allSolved(q))return false;return s.hints>0||Object.values(s.inputs||{}).some(v=>String(v).trim())||Object.values(s.gv||{}).some(v=>String(v).trim());});
function newAllHTML(){
  if(!state.allArm)return `<button class="btn btn-heat" data-act="newall" title="New numbers for all ${QS.length} ${CFG.noun||"questions"}">New numbers</button>`;
  return `<div class="arm-row" role="alert"><span class="small">This gives all ${QS.length} ${CFG.noun||"questions"} new numbers.${unfinished()?" Answers and hints you haven't finished will be cleared.":""}</span><button class="btn btn-primary btn-heat" data-act="newall">Ok</button><button class="btn btn-ghost" data-act="newallno">Cancel</button></div>`;
}
function renewAll(){if(CFG.onRenewAll)CFG.onRenewAll(true);QS.forEach(renew);if(CFG.onRenewAll)CFG.onRenewAll(false);}
/* Question list. In the wide two-column layout it's a plain list on the right. When it sits above the question
   (portrait or narrow screens) it becomes a dropdown: a button showing the current question, opening the full list. */
let pickOpen=false;
const CHEV='<svg viewBox="0 0 24 24" width="18" height="18" aria-hidden="true"><path d="M6 9.5l6 6 6-6"/></svg>';
function pickBtnHTML(){
  const i=state.cur,res=i>=QS.length,q=res?null:QS[i],done=!!q&&allSolved(q);
  const n=res?"Σ":done?"✓":i+1,t=res?"Results":q.topic,st=res?`${QS.filter(allSolved).length} of ${QS.length} solved`:statusOf(q);
  return `<button class="qpick-btn${done?" is-done":""}" data-act="pick" aria-expanded="${pickOpen}" aria-controls="qlist" aria-label="Choose a question: ${res?"Results":`question ${i+1}, ${t}`}"><span class="chip-n">${n}</span><span class="chip-t"><span class="chip-topic">${t}</span><span class="chip-s">${st}</span></span><span class="qpick-chev">${CHEV}</span></button>`;
}
function setPick(open){pickOpen=open;const el=$(".qpick");if(!el)return;el.classList.toggle("open",open);const bt=$(".qpick-btn",el);if(bt)bt.setAttribute("aria-expanded",String(open));
  if(open){const list=$("#qlist"),cur=$("#qlist .is-cur");if(list&&cur)list.scrollTop=Math.max(0,cur.offsetTop-list.clientHeight/2+cur.offsetHeight/2);}}
function sideHTML(){
  return `<div class="qpick${pickOpen?" open":""}">${pickBtnHTML()}<nav class="${CFG.sets?"setnav":"chips"} qlist" id="qlist" aria-label="Questions">${navHTML()}</nav></div>
    <div class="sheet-bar">${CFG.random?`<button class="btn" data-act="random">Random question</button>`:""}${CFG.newAll?newAllHTML():""}<button class="btn btn-ghost" data-act="sheet" aria-expanded="${state.sheetOpen}" aria-controls="sheet">${state.sheetOpen?"Hide":"Show"} my formula sheet<span class="count">${sheetEntries().length}</span></button></div>
    ${state.sheetOpen?sheetHTML():""}
`;
}
function givenHTML(q,s,p){
  const gl=q.given(p);
  const rows=gl.map(g=>{
    const id=`gv-${q.id}-${g.k}`,st=s.grevealed?true:s.gcheck[g.k];
    const v=s.grevealed?String(g.val):(s.gv[g.k]||"");
    const msg=(s.gmsg&&s.gmsg[g.k])||`${(s.gv[g.k]||"").trim()?"Not quite.":"Fill this one in."} ${g.look||`Look in the question for the number measured in ${g.unit}.`}`;
    return `<div class="gv-row${st===true?" ok":st===false?" bad":""}" data-row="${g.k}">
      <label class="gv-sym" for="${id}">${g.sym}</label><span class="gv-eq">=</span>
      <input id="${id}" class="gv-in" data-g="${g.k}" value="${esc(v)}" autocomplete="off" spellcheck="false" aria-describedby="${id}-d"${s.grevealed?" readonly":""}>
      <span class="unit">${g.unit||""}</span><span class="gv-mark" aria-hidden="true">${st===true?"✓":st===false?"✗":""}</span>
      <p class="gv-why" id="${id}-d"><b>${cap(g.name)}.</b> ${g.why}</p>
      ${st===false?`<p class="gv-hint">${msg}</p>`:""}
    </div>`;
  }).join("");
  const finds=val(q.find,p).map(f=>`<div class="gv-row"><span class="gv-sym">${f.sym}</span><span class="gv-eq">=</span><span class="gv-q">?</span><span class="unit">${f.unit||""}</span><span></span><p class="gv-why"><b>${cap(f.name)}.</b> ${f.why}</p></div>`).join("");
  const allOk=s.grevealed||gl.every(g=>s.gcheck[g.k]===true);
  let foot;
  if(s.grevealed) foot=`<p class="gv-msg">That's the full list. Now try the question, or open hint 2.</p>`;
  else if(allOk) foot=`<p class="gv-msg">All correct! This list is your starting point. Try the question now, or open hint 2.</p>`;
  else foot=`<div class="btn-row"><button class="btn" data-act="gcheck">Check my list</button><button class="btn btn-ghost" data-act="greveal">Fill it in for me</button></div>`;
  return `<p>${CFG.givenIntro||"Every physics problem starts the same way: list what you know. Each thing gets a <b>symbol</b>, a <b>value</b> and a <b>unit</b>. The numbers you need are now highlighted in the question. Type each one in the box next to its symbol. When you click a box, its number lights up in the question."}</p>
    <div class="gv"><span class="label">Given</span>${rows}<span class="label">Find</span>${finds}</div>${foot}`;
}
function rungBody(q,s,p,c,i){
  if(i===0) return givenHTML(q,s,p);
  if(i===1) return q.idea(p,c);
  if(i===2) return q.formula(p,c)+`<p class="added">✓ Added to your formula sheet (top of the page).</p>`;
  if(i===3) return q.plug(p,c);
  return q.solution(p,c);
}
function rungHTML(q,s,p,c,i){
  const n=i+1,r=RUNGS[i];
  const head=`<span class="rung-n">${n}</span><span class="rung-t"><span class="rung-title">${r[0]}</span><span class="rung-sub">${r[1]}</span></span>`;
  if(s.hints>=n){const folded=!!(s.folded&&s.folded[n]);  /* an opened hint folds away (and back) when you tap its title */
    return `<li class="rung is-open${folded?" is-folded":""}" id="rung-${n}"><button class="rung-head rung-toggle" data-act="fold" data-n="${n}" aria-expanded="${!folded}" aria-controls="rung-body-${n}">${head}<span class="rung-chev" aria-hidden="true">${CHEV}</span></button>${folded?"":`<div class="rung-body" id="rung-body-${n}">${rungBody(q,s,p,c,i)}</div>`}</li>`;}
  if(s.hints===i){
    if(n===5&&!allSolved(q)){
      if(!s.armed) return `<li class="rung" id="rung-${n}"><button class="rung-head rung-btn" data-act="arm">${head}<span class="rung-cta">Show solution</span></button></li>`;
      return `<li class="rung" id="rung-${n}"><div class="rung-head">${head}</div>
        <div class="guard" role="alert"><p><b>Before you look:</b> try once more using hint 4. It's fine to see the solution, but you remember a method much better when you finish it yourself.</p>
        <div class="btn-row"><button class="btn btn-primary" data-act="hint" data-n="5">Show the full solution</button><button class="btn btn-ghost" data-act="disarm">I'll try again first</button></div></div></li>`;
    }
    return `<li class="rung" id="rung-${n}"><button class="rung-head rung-btn" data-act="hint" data-n="${n}">${head}<span class="rung-cta">Open hint ${n}</span></button></li>`;
  }
  return `<li class="rung is-locked"><div class="rung-head">${head}</div></li>`;
}
function partHTML(q,s,part,p){
  const id=`ans-${q.id}-${part.id}`,fb=s.fb[part.id],ok=!!s.solved[part.id];
  return `<div class="part${ok?" is-solved":""}">
    <label class="part-label" for="${id}">${val(part.label,p)}</label>
    <div class="ans-row">
      <span class="ans-sym">${part.sym} =</span>
      <input id="${id}" class="ans" data-part="${part.id}" value="${esc(s.inputs[part.id]||"")}" placeholder="your answer" autocomplete="off" spellcheck="false" enterkeyhint="done"${ok?" readonly":""}>
      <span class="unit">${part.unit||""}</span>
      <button class="btn${ok?"":" btn-primary"}" data-act="check" data-part="${part.id}"${ok?" disabled":""}>${ok?"✓ Correct":"Check"}</button>
    </div>
    <div class="preview" id="pv-${part.id}" aria-live="polite">${ok?"":previewText(s.inputs[part.id])}</div>
    ${fb?`<div class="fb fb-${fb.kind}" role="status">${fb.msg}</div>`:""}
  </div>`;
}
function solvedHTML(q,s,p,c){
  const h=s.solvedWith||0;
  let line;
  if(s.usedSolution) line="You used the full solution this time. That's fine: press <b>New numbers</b> and try the same method again with fewer hints.";
  else if(h===0) line="No hints needed. Great work! Try <b>New numbers</b> to make sure it sticks, or move on.";
  else line=`You used ${h} hint${h>1?"s":""}. Press <b>New numbers</b> and try to solve it with ${h>1?"fewer hints":"no hints"}.`;
  const best=s.best!=null&&s.wins>1?` <span class="small">(Best so far: ${s.best} hint${s.best===1?"":"s"}.)</span>`:"";
  return `<div class="solved">
    <p class="solved-h">Solved</p>
    <p>${line}${best}</p>
    <div class="takeaway"><span class="tk-label">What you used</span>${EQ(q.takeEq(p,c))}<p>${q.takeaway}</p></div>
    <div class="hwlink"><span class="tk-label">${CFG.linkLabel||"On your homework"}</span><p>${val2(q.link,p,c)}</p></div>
    <div class="btn-row"><button class="btn" data-act="renew">New numbers</button><button class="btn btn-primary" data-act="next">${state.cur<QS.length-1?"Next question →":"See results →"}</button></div>
  </div>`;
}
function vizHTML(q,s,p,c){
  if(!q.viz||!(allSolved(q)||s.hints>=5)) return "";
  return `<section class="sec" aria-labelledby="viz-h"><div class="sec-head"><h2 id="viz-h">See it</h2></div><div id="viz-root" style="display:flex;flex-direction:column;gap:12px">${q.viz.html(p,c)}</div></section>`;
}
/* ---------- question scenes: an always-on animation of the situation (window.HL_SCENES, keyed by id or id/level) ---------- */
const sceneOf=q=>{const S=window.HL_SCENES||{};return q.scene||S[q.id+(q.level?"/"+q.level:"")]||S[q.id]||null;};
function sceneColors(){const cs=getComputedStyle(document.documentElement),v=(n,d)=>cs.getPropertyValue(n).trim()||d;
  return {ink:v("--ink","#14244a"),ink2:v("--ink-2","#55637f"),blue:v("--blue","#2346a8"),blueSoft:v("--blue-soft","#e7edfa"),heat:v("--heat","#d4602a"),
    marker:v("--marker","#fbe26a"),rule:v("--rule","#d3dbe8"),bg:v("--card-2","#f6f8fd"),card:v("--card","#fff"),ok:v("--ok","#16714a"),bad:v("--bad","#b8352b")};}
function makeKit(g,W,H){
  const K={g,W,H,col:sceneColors()};
  const C=x=>K.col[x]||x;
  const paint=o=>{if(o.fill){g.fillStyle=C(o.fill);g.fill();}if(o.c!==false){g.strokeStyle=C(o.c||"ink");g.lineWidth=o.w||2;g.lineJoin="round";g.lineCap="round";g.setLineDash(o.dash||[]);g.stroke();}};
  const wrap=(o,fn)=>{g.save();if(o&&o.alpha!=null)g.globalAlpha=Math.max(0,Math.min(1,o.alpha));fn();g.restore();};
  K.line=(x1,y1,x2,y2,o={})=>wrap(o,()=>{g.beginPath();g.moveTo(x1,y1);g.lineTo(x2,y2);paint(Object.assign({},o,{fill:null}));});
  K.poly=(pts,o={})=>wrap(o,()=>{if(pts.length<2)return;g.beginPath();pts.forEach((q,i)=>i?g.lineTo(q[0],q[1]):g.moveTo(q[0],q[1]));if(o.close)g.closePath();paint(o);});
  K.circle=(x,y,r,o={})=>wrap(o,()=>{g.beginPath();g.arc(x,y,Math.max(0,r),0,Math.PI*2);paint(o);});
  K.arc=(x,y,r,a0,a1,o={})=>wrap(o,()=>{g.beginPath();g.arc(x,y,Math.max(0,r),a0,a1,!!o.ccw);paint(Object.assign({},o,{fill:null}));});
  K.ellipse=(x,y,rx,ry,o={})=>wrap(o,()=>{g.beginPath();g.ellipse(x,y,Math.max(0,rx),Math.max(0,ry),o.rot||0,0,Math.PI*2);paint(o);});
  K.rect=(x,y,w,h,o={})=>wrap(o,()=>{g.beginPath();const r=Math.min(o.r||0,Math.abs(w)/2,Math.abs(h)/2);if(r&&g.roundRect)g.roundRect(x,y,w,h,r);else g.rect(x,y,w,h);paint(o);});
  K.arrow=(x1,y1,x2,y2,o={})=>{const a=Math.atan2(y2-y1,x2-x1),L=Math.hypot(x2-x1,y2-y1);if(L<2)return;const hs=Math.min(o.head||9,L*0.6);
    K.line(x1,y1,x2-Math.cos(a)*hs*0.6,y2-Math.sin(a)*hs*0.6,{c:o.c,w:o.w||2.2,dash:o.dash,alpha:o.alpha});
    K.poly([[x2,y2],[x2-hs*Math.cos(a-0.42),y2-hs*Math.sin(a-0.42)],[x2-hs*Math.cos(a+0.42),y2-hs*Math.sin(a+0.42)]],{fill:o.c||"ink",c:false,close:true,alpha:o.alpha});};
  const font=o=>`${o.italic?"italic ":""}${o.bold?"700 ":""}${(o.size||13)*(K.ts||1)}px ${o.serif?'"STIX Two Text",Cambria,"Times New Roman",serif':'"Atkinson Hyperlegible","Segoe UI",system-ui,sans-serif'}`;
  K.text=(s,x,y,o={})=>wrap(o,()=>{g.fillStyle=C(o.c||"ink");g.font=font(o);g.textAlign=o.align||"center";g.textBaseline=o.base||"middle";g.fillText(s,x,y);});
  K.tag=(s,x,y,o={})=>{g.save();g.font=font({size:o.size||12});const w=g.measureText(s).width+12,h=(o.size||12)*(K.ts||1)+9;g.restore();
    const ax=o.align==="left"?x:o.align==="right"?x-w:x-w/2;
    K.rect(ax,y-h/2,w,h,{fill:"card",c:o.c||"ink2",w:1,r:4,alpha:o.alpha});K.text(s,ax+w/2,y+0.5,{c:o.c||"ink",size:o.size||12,alpha:o.alpha});};
  K.ground=(y,x1=0,x2=W,o={})=>{K.line(x1,y,x2,y,{c:o.c||"ink",w:2});for(let x=x1+6;x<x2;x+=12)K.line(x,y+2,x-7,y+10,{c:"rule",w:1.2});};
  K.wall=(x,y1,y2)=>{K.line(x,y1,x,y2,{w:3});for(let y=y1+3;y<y2;y+=10)K.line(x,y,x-8,y+7,{c:"rule",w:1.2});};
  K.ceiling=(y,x1,x2)=>{K.line(x1,y,x2,y,{w:3});for(let x=x1+3;x<x2;x+=10)K.line(x,y,x+7,y-8,{c:"rule",w:1.2});};
  K.spring=(x1,y1,x2,y2,o={})=>{const n=o.coils||12,amp=o.amp||8,dx=x2-x1,dy=y2-y1,L=Math.hypot(dx,dy)||1,ux=dx/L,uy=dy/L,nx=-uy,ny=ux,lead=Math.min(10,L*0.15);
    const pts=[[x1,y1],[x1+ux*lead,y1+uy*lead]];for(let i=0;i<n;i++){const d=lead+(L-2*lead)*(i+0.5)/n,sd=i%2?1:-1;pts.push([x1+ux*d+nx*amp*sd,y1+uy*d+ny*amp*sd]);}
    pts.push([x2-ux*lead,y2-uy*lead],[x2,y2]);K.poly(pts,{c:o.c||"blue",w:o.w||2});};
  K.wheel=(x,y,r,ang,o={})=>{K.circle(x,y,r,{fill:"card",c:o.c||"ink",w:2});for(let i=0;i<3;i++){const a=ang+i*Math.PI/3;K.line(x-Math.cos(a)*r*0.78,y-Math.sin(a)*r*0.78,x+Math.cos(a)*r*0.78,y+Math.sin(a)*r*0.78,{c:o.c||"ink",w:1.2});}};
  K.car=(x,y,o={})=>{const s=o.s||1,ang=o.ang||0,body=o.body||"blue";
    K.poly([[x-22*s,y-29*s],[x-14*s,y-44*s],[x+12*s,y-44*s],[x+23*s,y-29*s]],{fill:body,c:"ink",w:1.5,close:true});
    K.rect(x-37*s,y-30*s,74*s,19*s,{fill:body,c:"ink",w:1.5,r:5*s});
    K.poly([[x-17*s,y-31*s],[x-11*s,y-41*s],[x-2*s,y-41*s],[x-2*s,y-31*s]],{fill:"card",c:false,close:true,alpha:0.9});
    K.poly([[x+2*s,y-31*s],[x+2*s,y-41*s],[x+10*s,y-41*s],[x+18*s,y-31*s]],{fill:"card",c:false,close:true,alpha:0.9});
    K.rect(x+32*s,y-27*s,5*s,4*s,{fill:"marker",c:false});K.rect(x-38*s,y-27*s,4*s,6*s,{fill:o.brake?"bad":"rule",c:false});
    if(o.brake)K.circle(x-40*s,y-24*s,6*s,{fill:"bad",c:false,alpha:0.25});
    K.wheel(x-21*s,y-9*s,9*s,ang);K.wheel(x+21*s,y-9*s,9*s,ang);};
  K.person=(x,y,o={})=>{const s=o.s||1,c=o.c||"ink",lean=o.lean||0;const hx=x+lean*s;
    K.circle(hx,y-58*s,7*s,{fill:"card",c,w:2});K.line(hx,y-51*s,x,y-24*s,{c,w:2.4});K.line(x,y-24*s,x-8*s,y,{c,w:2.4});K.line(x,y-24*s,x+8*s,y,{c,w:2.4});
    (o.arms||[[-12,-30],[12,-30]]).forEach(a=>K.line(hx+(x-hx)*0.25,y-45*s,x+a[0]*s,y+a[1]*s,{c,w:2}));};
  K.dim=(x1,x2,y,label,o={})=>{const c=o.c||"ink2";K.line(x1,y,x2,y,{c,w:1.2});K.line(x1,y-5,x1,y+5,{c,w:1.2});K.line(x2,y-5,x2,y+5,{c,w:1.2});if(label)K.tag(label,(x1+x2)/2,y,{size:11});};
  K.vdim=(x,y1,y2,label,o={})=>{const c=o.c||"ink2";K.line(x,y1,x,y2,{c,w:1.2});K.line(x-5,y1,x+5,y1,{c,w:1.2});K.line(x-5,y2,x+5,y2,{c,w:1.2});if(label)K.tag(label,x,(y1+y2)/2,{size:11});};
  K.ease=u=>u<=0?0:u>=1?1:u*u*(3-2*u);
  K.clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
  K.mod=(a,b)=>((a%b)+b)%b;
  K.fmt=fmt;
  return K;
}
function setupScene(q){
  const sc=sceneOf(q),cv=$("#scene-cv");if(!sc||!cv||!cv.getContext)return;
  const g=cv.getContext("2d");if(!g)return;
  const p=state.qs[q.id].params,c=q.calc(p),W=600,H=sc.h||220,K=makeKit(g,W,H);
  let scale=1,t=0,visible=true,frame=0;
  const size=()=>{const r=cv.getBoundingClientRect(),dpr=Math.min(2,window.devicePixelRatio||1),w=Math.max(1,r.width);cv.width=Math.round(w*dpr);cv.height=Math.round(w*H/W*dpr);scale=cv.width/W;K.ts=Math.max(1,Math.min(1.6,9.5/(11*w/W)));};
  const draw=tt=>{g.setTransform(1,0,0,1,0,0);g.clearRect(0,0,cv.width,cv.height);g.setTransform(scale,0,0,scale,0,0);
    try{sc.draw(K,tt,p,c);}catch(e){(window.__sceneErrs=window.__sceneErrs||[]).push(q.id+": "+(e&&e.message||e));}};
  size();
  const onResize=()=>{size();draw(t);};window.addEventListener("resize",onResize);cleanups.push(()=>window.removeEventListener("resize",onResize));
  if("IntersectionObserver" in window){const io=new IntersectionObserver(es=>{visible=es[0].isIntersecting;});io.observe(cv);cleanups.push(()=>io.disconnect());}
  if(sc.reset)sc.reset();
  if(reduceMotion){draw(sc.still!=null?sc.still:1.5);return;}
  draw(0);
  makeLoop(dt=>{t+=dt;if(++frame%30===0)K.col=sceneColors();if(visible)draw(t);});
}
function setupViz(q){
  const root=$("#viz-root");if(!root||!q.viz||!q.viz.setup)return;
  const p=state.qs[q.id].params;
  q.viz.setup(p,q.calc(p),{$:sel=>$(sel,root),$$:sel=>$$(sel,root),root,loop:makeLoop,reduceMotion,fmt});
}
function questionHTML(q){
  const s=state.qs[q.id],p=s.params,c=q.calc(p),gl=q.given(p);
  const G=(k,txt)=>{const g=gl.find(x=>x.k===k);return `<mark class="g${s.hints>=1?" on":""}" data-g="${k}">${s.grevealed&&g&&CFG.gsym!==false?`<span class="g-sym">${g.sym} =</span> `:""}${txt}</mark>`;};
  const T=(k,txt)=>`<button type="button" class="term${s.term===k?" is-on":""}" data-act="term" data-k="${k}" aria-expanded="${s.term===k}">${txt}</button>`;
  const def=s.term&&q.terms&&q.terms[s.term]?`<div class="termdef" role="note"><p><b>${q.terms[s.term][0]}.</b> ${q.terms[s.term][1]}</p><button class="btn btn-ghost" data-act="term" data-k="${s.term}">Close</button></div>`:"";
  const idx=QS.indexOf(q);
  return `<div style="display:flex;flex-direction:column;gap:22px">
    <article class="qcard" aria-labelledby="q-title">
      <div class="q-meta"><span class="tk-label" id="q-title">Question ${idx+1} of ${QS.length}</span><span class="tag">${q.topic}</span>${q.level?`<span class="tag tag-set">${q.level}</span>`:""}${CFG.sets&&q.set?`<span class="tag tag-set">${setLabel(q.set)}</span>`:""}<span class="small">${q.hw||""}</span></div>
      <p class="qtext">${q.text(p,G,T)}</p>${q.after?q.after(p,c,allSolved(q)):""}
      ${sceneOf(q)?`<div class="scene" aria-hidden="true"><canvas id="scene-cv"></canvas></div>`:""}
      <p class="small" style="margin-top:-8px">Words with a dotted underline explain themselves when you click them.</p>
      ${def}
      <div class="answers">
        ${q.parts.map(pt=>partHTML(q,s,pt,p)).join("")}
        ${allSolved(q)?"":`<p class="calc-note">${CFG.calcNote||"You can type a number (like 13 or 0.31) or a whole calculation (like <code>4+1.5*6</code>, <code>sqrt(16)</code> or <code>2*pi</code>)."}</p>`}
      </div>
      ${allSolved(q)?solvedHTML(q,s,p,c):""}
    </article>
    <section class="sec" aria-labelledby="hints-h">
      <div class="sec-head"><h2 id="hints-h">Hints</h2>
        <p class="sec-note">Open one hint, then try again. Only open the next one if you're still stuck.</p>
        <details class="why"><summary>Why this order?</summary><p>Each hint adds the smallest piece of help that might get you unstuck. Listing what you know comes first, because that is where most problems go wrong. The idea comes before the formula, so you know <i>why</i> the formula fits and can recognise it in other questions. Plugging in the numbers comes next, so you still do the last step yourself. The full solution is last, for when you really need it.</p></details>
      </div>
      <ol class="ladder">${RUNGS.map((r,i)=>rungHTML(q,s,p,c,i)).join("")}</ol>
    </section>
    ${vizHTML(q,s,p,c)}
    <nav class="qnav" aria-label="Question navigation">
      ${idx>0?`<button class="btn" data-act="prev">← Previous</button>`:"<span></span>"}
      <button class="btn" data-act="next">${idx<QS.length-1?"Next question →":"See results →"}</button>
    </nav>
  </div>`;
}
function summaryHTML(){
  const n=QS.filter(allSolved).length;
  const rows=QS.map((q,i)=>{const s=state.qs[q.id],done=allSolved(q);
    return `<tr><td>${i+1}. ${q.topic}${CFG.sets&&q.set?` <span class="small">· ${setLabel(q.set)}</span>`:""}</td><td class="${done?"st-ok":"st-open"}">${done?"Solved":"Not yet"}</td><td>${done?(s.usedSolution?"Full solution":`${s.solvedWith} hint${s.solvedWith===1?"":"s"}`):(s.hints?`${s.hints} open`:"—")}</td><td>${s.best!=null?`${s.best} hint${s.best===1?"":"s"}`:"—"}</td></tr>`;}).join("");
  return `<div style="display:flex;flex-direction:column;gap:22px">
    <article class="qcard" aria-labelledby="sum-h">
      <h2 id="sum-h">${n===QS.length?`All ${QS.length} solved`:`${n} of ${QS.length} solved`}</h2>
      <div class="tbl-wrap"><table class="sum-tbl"><thead><tr><th>Question</th><th>Status</th><th>This round</th><th>Best</th></tr></thead><tbody>${rows}</tbody></table></div>
      <div class="btn-row"><button class="btn btn-primary" data-act="renewall">Practise all ${QS.length} with new numbers</button><button class="btn" data-act="go" data-i="0">Back to question 1</button></div>
    </article>
  </div>`;
}
function render(){
  resolve();
  stopLoops();
  $("#top").innerHTML=headHTML();$("#side").innerHTML=sideHTML();
  const main=$("#main");
  if(state.cur>=QS.length) main.innerHTML=summaryHTML();
  else{main.innerHTML=questionHTML(QS[state.cur]);setupViz(QS[state.cur]);setupScene(QS[state.cur]);}
  save();
}
function scrollToEl(el,block){if(el)el.scrollIntoView({behavior:reduceMotion?"auto":"smooth",block:block||"nearest"});}

/* ---------- actions ---------- */
const curQ=()=>QS[state.cur];
function checkPart(q,partId){
  const s=state.qs[q.id],p=s.params,c=q.calc(p),part=q.parts.find(x=>x.id===partId);
  const raw=s.inputs[partId]||"",xs=candidates(raw),ans=part.ans(p,c);
  const tol=part.tol!=null?part.tol:0.02,abs=part.abs||1e-9,F=part.fmt||fmt;
  const ok=(x,y)=>Number.isFinite(x)&&Number.isFinite(y)&&Math.abs(x-y)<=Math.abs(y)*tol+abs;
  if(!xs.length){
    s.fb[partId]={kind:"info",msg:raw.trim()?"I can't read that. Type a number (like 13 or 0.31) or a calculation (like 4+1.5*6).":"Type your answer first."};
  } else if(xs.some(x=>ok(x,ans))){
    s.solved[partId]=true;
    s.fb[partId]={kind:"ok",msg:`<b>Correct!</b> ${part.sym} = ${F(ans)} ${part.unit||""}`};
  } else {
    const traps=part.traps?part.traps(p,c):[];let msg=null;
    for(const x of xs){const t=traps.find(tr=>ok(x,tr[0]));if(t){msg=t[1];break;}}
    const x=xs[0];
    if(msg) s.fb[partId]={kind:"bad",msg};
    else if(ok(-x,ans)) s.fb[partId]={kind:"bad",msg:`The size is right, but check the sign. This value should be ${ans<0?"negative":"positive"}.`};
    else if(near(x,ans,0.06)) s.fb[partId]={kind:"close",msg:part.closeMsg||CFG.closeMsg||"Very close! Check your rounding. Keep at least 3 significant figures (for example 0.314, not 0.3)."};
    else{
      const nxt=s.hints<5?` If you're stuck, open hint ${s.hints+1} (${RUNGS[s.hints][0].toLowerCase()}).`:" Compare your steps with the full solution above.";
      s.fb[partId]={kind:"bad",msg:`Not quite. Check your calculation.${nxt}`};
    }
  }
  if(allSolved(q)&&!s.roundDone){
    s.roundDone=true;s.solvedWith=s.hints;s.wins=(s.wins||0)+1;
    const score=s.usedSolution?5:s.hints;
    s.best=s.best==null?score:Math.min(s.best,score);
  }
  render();
  if(allSolved(q)) scrollToEl($(".solved"),"center");
  else{const el=$(`#ans-${q.id}-${partId}`);if(el&&!s.solved[partId])el.focus();
    if(s.solved[partId]){const nextIn=$$(".ans").find(i=>!i.readOnly);if(nextIn)nextIn.focus();}}
}
function renew(q){
  const s=state.qs[q.id],sl=SLOTS.find(x=>x.id===q.id);let def=q,w;
  if(sl&&sl.pool){w=Math.floor(Math.random()*sl.pool.length);def=sl.pool[w];}
  let np,tries=0;
  do{np=def.random();tries++;}while((w===undefined||w===(s.which||0))&&JSON.stringify(np)===JSON.stringify(s.params)&&tries<20);
  const f=freshQ(def,np);f.best=s.best;f.wins=s.wins;if(w!==undefined)f.which=w;state.qs[q.id]=f;resolve();
}
function onClick(e){
  if(pickOpen&&!e.target.closest(".qpick"))setPick(false);
  const b=e.target.closest("[data-act]");if(!b)return;
  const act=b.dataset.act,q=curQ(),s=q?state.qs[q.id]:null;
  if(act==="pick"){setPick(!pickOpen);return;}
  pickOpen=false;
  if(state.allArm&&act!=="newall"&&act!=="newallno")state.allArm=false;
  switch(act){
    case "newall":if(!state.allArm){state.allArm=true;render();break;}
      state.allArm=false;renewAll();if(state.cur>=QS.length)state.cur=0;render();scrollToEl($("#main"),"start");break;
    case "newallno":state.allArm=false;render();break;
    case "theme":{const next=isDark()?"light":"dark";document.documentElement.setAttribute("data-theme",next);try{localStorage.setItem(THEME_KEY,next);}catch(e){}render();break;}
    case "go":state.cur=+b.dataset.i;render();scrollToEl($("#main"),"start");break;
    case "next":state.cur=Math.min(QS.length,state.cur+1);render();scrollToEl($("#main"),"start");break;
    case "prev":state.cur=Math.max(0,state.cur-1);render();scrollToEl($("#main"),"start");break;
    case "sheet":state.sheetOpen=!state.sheetOpen;render();break;
    case "random":{let pool=QS.map((x,i)=>i).filter(i=>i!==state.cur&&!allSolved(QS[i]));if(!pool.length)pool=QS.map((x,i)=>i).filter(i=>i!==state.cur);state.cur=pick(pool);render();scrollToEl($("#main"),"start");break;}
    case "term":s.term=s.term===b.dataset.k?null:b.dataset.k;render();break;
    case "arm":s.armed=true;render();scrollToEl($("#rung-5"));break;
    case "disarm":s.armed=false;render();break;
    case "fold":{const n=+b.dataset.n;s.folded=s.folded||{};s.folded[n]=!s.folded[n];render();const t=$(`#rung-${n} .rung-toggle`);if(t)t.focus({preventScroll:true});break;}
    case "hint":{const n=+b.dataset.n;if(s.folded)delete s.folded[n];if(n===s.hints+1){s.hints=n;s.armed=false;if(n===5&&!allSolved(q))s.usedSolution=true;}
      render();scrollToEl($(`#rung-${n}`),"start");
      if(n===1){const first=$(".gv-in");if(first&&!s.grevealed)setTimeout(()=>first.focus({preventScroll:true}),reduceMotion?0:350);}break;}
    case "gcheck":{s.gmsg=s.gmsg||{};q.given(s.params).forEach(g=>{const xs=candidates(s.gv[g.k]||"");const ok=xs.some(x=>near(x,g.val,0.005));s.gcheck[g.k]=ok;s.gmsg[g.k]=null;
        if(!ok&&g.gtraps){const t=g.gtraps.find(tr=>xs.some(x=>near(x,tr[0],0.005)));if(t)s.gmsg[g.k]=t[1];}});
      render();scrollToEl($("#rung-1"));break;}
    case "greveal":s.grevealed=true;render();break;
    case "check":checkPart(q,b.dataset.part);break;
    case "renew":renew(q);render();scrollToEl($("#main"),"start");break;
    case "renewall":state.allArm=false;renewAll();state.cur=0;render();scrollToEl($("#main"),"start");break;
  }
}
function onInput(e){
  const t=e.target,q=curQ();if(!q)return;const s=state.qs[q.id];
  if(t.classList.contains("ans")){s.inputs[t.dataset.part]=t.value;const pv=$(`#pv-${t.dataset.part}`);if(pv)pv.textContent=previewText(t.value);save();}
  else if(t.classList.contains("gv-in")){s.gv[t.dataset.g]=t.value;if(s.gcheck[t.dataset.g]!==undefined){delete s.gcheck[t.dataset.g];const row=t.closest(".gv-row");if(row){row.classList.remove("ok","bad");const m=$(".gv-mark",row);if(m)m.textContent="";const h=$(".gv-hint",row);if(h)h.remove();}}save();}
}
function onKey(e){
  if(e.key==="Escape"&&pickOpen){setPick(false);const bt=$(".qpick-btn");if(bt)bt.focus();return;}
  if(e.key!=="Enter")return;const t=e.target,q=curQ();if(!q||!t.classList)return;
  if(t.classList.contains("ans")&&!t.readOnly){e.preventDefault();checkPart(q,t.dataset.part);}
  else if(t.classList.contains("gv-in")){e.preventDefault();const b=$('[data-act="gcheck"]');if(b)b.click();}
}
let bound=false;
function bind(){
  if(bound)return;bound=true;
  document.addEventListener("click",onClick);
  document.addEventListener("input",onInput);
  document.addEventListener("keydown",onKey);
  document.addEventListener("focusin",e=>{const t=e.target;if(t.classList&&t.classList.contains("gv-in"))$$("mark.g").forEach(m=>m.classList.toggle("lit",m.dataset.g===t.dataset.g));});
  document.addEventListener("focusout",e=>{const t=e.target;if(t.classList&&t.classList.contains("gv-in"))$$("mark.g.lit").forEach(m=>m.classList.remove("lit"));});
}

/* ---------- authoring checks ---------- */
function selfTest(){
  const out=[],BAD=/undefined|NaN|\[object |Infinity|=>/;
  const REQ=["id","topic","base","random","calc","text","given","find","parts","idea","formula","plug","solution","sheet","takeEq","takeaway","link"];
  const ids=new Set();
  allDefs().forEach(q=>{
    REQ.forEach(k=>{if(q[k]==null)out.push(`${q.id||"?"}: missing field "${k}"`);});
    if(ids.has(q.id))out.push(`duplicate question id "${q.id}"`);ids.add(q.id);
    const seen=new Set(),vars=[q.base];for(let i=0;i<60;i++)vars.push(q.random());
    vars.forEach(p=>{const key=JSON.stringify(p);if(seen.has(key))return;seen.add(key);
      try{
        const c=q.calc(p),gl=q.given(p),keys=new Set(gl.map(g=>g.k));
        const txt=q.text(p,(k,t)=>{if(!keys.has(k))out.push(`${q.id}: text marks "${k}" but given() has no such key`);return t;},(k,t)=>{if(!q.terms||!q.terms[k])out.push(`${q.id}: text uses term "${k}" that is missing from terms`);return t;});
        const html=[txt,q.after?q.after(p,c,false):"",q.idea(p,c),q.formula(p,c),q.plug(p,c),q.solution(p,c),q.takeEq(p,c),q.takeaway,val2(q.link,p,c),q.viz?q.viz.html(p,c):""]
          .concat(q.sheet.map(e=>e.eq+" "+(e.note||""))).concat(val(q.find,p).map(f=>f.sym+" "+f.why)).concat(q.parts.map(pt=>val(pt.label,p))).join(" ");
        const m=html.match(BAD);if(m)out.push(`${q.id} ${key}: generated text contains "${m[0]}"`);
        gl.forEach(g=>{if(!Number.isFinite(g.val))out.push(`${q.id} ${key}: given "${g.k}" is not a number`);
          (g.gtraps||[]).forEach(t=>{if(near(t[0],g.val,0.005))out.push(`${q.id} ${key}: given "${g.k}" trap equals the right value`);});});
        q.parts.forEach(pt=>{const a=pt.ans(p,c);
          if(!Number.isFinite(a)){out.push(`${q.id} ${key}: part "${pt.id}" answer is not a number`);return;}
          (pt.traps?pt.traps(p,c):[]).forEach(([v,msg],i)=>{
            if(!Number.isFinite(v))out.push(`${q.id} ${key}: part "${pt.id}" trap ${i+1} is not a number`);
            else if(Math.abs(v-a)<=Math.abs(a)*(pt.tol!=null?pt.tol:0.025)+(pt.abs||1e-9))out.push(`${q.id} ${key}: part "${pt.id}" trap ${i+1} (${fmt(v)}) is too close to the answer (${fmt(a)}), so it can never fire`);
            const mm=String(msg).match(BAD);if(mm)out.push(`${q.id}: part "${pt.id}" trap ${i+1} message contains "${mm[0]}"`);});
        });
      }catch(e){out.push(`${q.id} ${key}: threw ${e&&e.message||e}`);}
    });
  });
  return out;
}
const debug={
  answers:()=>QS.map(q=>{const s=state.qs[q.id],c=q.calc(s.params);return q.parts.map(pt=>({input:`#ans-${q.id}-${pt.id}`,part:pt.id,value:pt.ans(s.params,c)}));}),
  reset:()=>{try{localStorage.removeItem(STORE);}catch(e){}}
};

/* ---------- start ---------- */
function start(cfg){
  CFG=cfg||{};SLOTS=CFG.questions||[];RUNGS=CFG.rungs||DEFAULT_RUNGS;STORE="physics-hint-ladder-"+(CFG.id||"set");
  if(!$("#top")){const w=document.createElement("div");w.className="wrap";w.innerHTML='<div id="top"></div><aside id="side" aria-label="Question list"></aside><main id="main"></main>';document.body.appendChild(w);}
  if(!$("#side")){const a=document.createElement("aside");a.id="side";a.setAttribute("aria-label","Question list");$("#top").after(a);}
  try{const raw=localStorage.getItem(STORE);if(raw){const s=JSON.parse(raw);if(s&&s.qs)state=s;}}catch(e){}
  if(!state)state={cur:0,sheetOpen:false,qs:{}};
  SLOTS.forEach(sl=>{const s=state.qs[sl.id];
    if(s&&s.params&&(!sl.pool||((s.which||0)<sl.pool.length)))return;
    if(sl.pool){const w=Math.floor(Math.random()*sl.pool.length),f=freshQ(sl.pool[w]);f.which=w;state.qs[sl.id]=f;}
    else state.qs[sl.id]=freshQ(sl);});
  resolve();
  if(!(state.cur>=0&&state.cur<=QS.length))state.cur=0;
  if(CFG.themeToggle){try{const t=localStorage.getItem(THEME_KEY);if(t==="light"||t==="dark")document.documentElement.setAttribute("data-theme",t);}catch(e){}
    if(window.matchMedia){const mq=window.matchMedia("(prefers-color-scheme: dark)"),f=()=>{if(!document.documentElement.getAttribute("data-theme"))render();};if(mq.addEventListener)mq.addEventListener("change",f);}}
  bind();render();
}

window.HL={
  version:8,start,selfTest,debug,
  fmt,pick,near,
  mi,up,sb,ssp,OP,FR,SQ,EQ,CALC,HALF,sq2,neg,IMPLIES,AND,PAREN,PI,OMEGA,V0,VI,VF,KE,KEI,KEF,DKE,
  legend,steps,checkline,finalAns,watch,calcTip,
  viz:{slider:vizSlider,spring:vizSpring}
};
})();
