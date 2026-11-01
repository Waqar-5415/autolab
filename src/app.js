// AutoLab UI layer
import {EPS,E,parse,astTxt,thompson,subset,minimize,elim,simulate,equiv,enumerate,nfaOf,startId,F,lbl,adjOf} from './algorithms.js';
const $=s=>document.querySelector(s),esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
/* ---------- layout & drawing ---------- */
function layout(A){const adj={},lv={},P={};A.transitions.forEach(t=>(adj[t.from]??=[]).push(t.to));
const bfs=r=>{lv[r]??=0;const q=[r];while(q.length){const x=q.shift();(adj[x]||[]).forEach(y=>{if(!(y in lv)){lv[y]=lv[x]+1;q.push(y)}})}};
A.states.filter(s=>s.isStart).forEach(s=>bfs(s.id));A.states.forEach(s=>{if(!(s.id in lv))bfs(s.id)});
const cols={};A.states.forEach(s=>(cols[lv[s.id]]??=[]).push(s.id));
for(const l in cols)cols[l].forEach((id,i)=>P[id]={x:90+l*130,y:240+(i-(cols[l].length-1)/2)*100,l:+l});return P}
const SC='.nd circle{stroke:var(--edge);stroke-width:2;fill:var(--card)}.nd .in{fill:none}.nd text{fill:var(--tx);font:600 12px Inter,sans-serif;text-anchor:middle;dominant-baseline:central;pointer-events:none}.nd{cursor:grab}.nd.on circle:first-of-type{stroke:var(--ac);stroke-width:3.5;filter:drop-shadow(0 0 7px var(--ac));animation:pu .8s}.nd.red circle:first-of-type{stroke:var(--er);stroke-width:4;filter:drop-shadow(0 0 7px var(--er))}.nd.hv circle:first-of-type{stroke:var(--ac2);stroke-width:3.5}.dd{opacity:.5}.sa{stroke:var(--ok);stroke-width:2.5;fill:none}.ed{fill:none;stroke:var(--edge);stroke-width:1.6}.ed.h{stroke:var(--ac);stroke-width:3}.el{font:600 12px Inter,sans-serif;fill:var(--tx);text-anchor:middle;paint-order:stroke;stroke:var(--card);stroke-width:4px}@keyframes pu{from{stroke-width:10}}';
const mkr=(i,c)=>`<marker id="${i}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0L10,5L0,10z" style="fill:${c}"/></marker>`;
let vb={x:0,y:0,w:800,h:470};
function drawSVG(A,P,hl,hide){const vs=A.states.filter(s=>!(hide&&s.meta?.dead)),vi=new Set(vs.map(s=>s.id)),g={};let o='';
A.transitions.forEach(t=>{if(vi.has(t.from)&&vi.has(t.to))(g[t.from+'>'+t.to]??=[]).push(t.symbol)});
for(const k in g){const[f,t]=k.split('>').map(Number),a=P[f],b=P[t],lb=esc([...new Set(g[k])].join(',')),h=(hl.e||[]).includes(k)?' h':'';let d,lx,ly;
if(f===t){d=`M${a.x-12},${a.y-18}C${a.x-36},${a.y-64} ${a.x+36},${a.y-64} ${a.x+12},${a.y-18}`;lx=a.x;ly=a.y-58}
else{const dx=b.x-a.x,dy=b.y-a.y,L=Math.hypot(dx,dy)||1,off=g[t+'>'+f]?34:(Math.abs(a.l-b.l)===1?0:40),cx=(a.x+b.x)/2-dy/L*off*2,cy=(a.y+b.y)/2+dx/L*off*2,u=(px,py,qx,qy,r)=>{const m=Math.hypot(qx-px,qy-py)||1;return[px+(qx-px)/m*r,py+(qy-py)/m*r]},[sx,sy]=u(a.x,a.y,cx,cy,20),[ex,ey]=u(b.x,b.y,cx,cy,23);d=`M${sx},${sy}Q${cx},${cy} ${ex},${ey}`;lx=(sx+2*cx+ex)/4;ly=(sy+2*cy+ey)/4-5}
o+=`<path class="ed${h}" d="${d}" marker-end="url(#${h?'arh':'ar'})"/><text class="el" x="${lx}" y="${ly}">${lb}</text>`}
vs.forEach(s=>{const p=P[s.id],c=hl.col&&hl.col[s.id],cl=['nd',(hl.s||[]).includes(s.id)&&'on',(hl.r||[]).includes(s.id)&&'red',s.meta?.dead&&'dd'].filter(Boolean).join(' ');
o+=`<g class="${cl}" data-id="${s.id}" transform="translate(${p.x},${p.y})" tabindex="0" role="img" aria-label="State ${esc(s.label)}${s.isStart?', start':''}${s.isAccept?', accepting':''}"><title>${esc(s.label)}${s.meta?.set?' = NFA '+s.meta.set:''}${s.meta?.members?' = '+s.meta.members:''}${s.meta?.dead?' (dead state)':''}</title>${s.isStart?'<path class="sa" d="M-60,0H-25" marker-end="url(#arg)"/>':''}<circle r="20"${c!==undefined?` style="fill:hsl(${c*67%360} 70% 60%/.4)"`:''}/>${s.isAccept?'<circle class="in" r="15"/>':''}<text>${esc(s.label)}</text></g>`});
return`<svg xmlns="http://www.w3.org/2000/svg" viewBox="${vb.x} ${vb.y} ${vb.w} ${vb.h}" role="img" aria-label="Automaton diagram"><style>${SC}</style><defs>${mkr('ar','var(--edge)')}${mkr('arh','var(--ac)')}${mkr('arg','var(--ok)')}</defs>${o}</svg>`}
/* ---------- app state ---------- */
const pages={r:{stages:[],si:1,idx:0,sims:[]},f:{stages:[],si:0,idx:0,sims:[]}},PT=[['tbl','Table'],['stp','Steps'],['sub','Subset'],['par','Partitions'],['sim','Simulator']],pos=new WeakMap;
let tab='r',ptab='tbl',needFit=true,timer=null,drag=null;
const pg=()=>pages[tab],steps=()=>{const p=pg();return p.over||p.stages[p.si]?.steps||[]},cur=()=>steps()[pg().idx];
function toast(m,k){const t=$('#toast');t.textContent=m;t.style.background=k==='bad'?'#dc2626':'#16a34a';t.classList.add('on');clearTimeout(toast.t);toast.t=setTimeout(()=>t.classList.remove('on'),3200)}
function fit(P,A){const hide=$('#hd').checked,xs=[],ys=[];A.states.forEach(s=>{if(P[s.id]&&!(hide&&s.meta?.dead)){xs.push(P[s.id].x);ys.push(P[s.id].y)}});if(!xs.length)return;
const x0=Math.min(...xs)-90,x1=Math.max(...xs)+60,y0=Math.min(...ys)-90,y1=Math.max(...ys)+50,h=$('#cvh'),asp=(h.clientWidth||800)/(h.clientHeight||470);let w=x1-x0,hh=y1-y0;if(w/hh<asp)w=hh*asp;else hh=w/asp;vb={x:(x0+x1)/2-w/2,y:(y0+y1)/2-hh/2,w,h:hh};needFit=false}
function draw(){const st=cur(),h=$('#cvh');if(!st){h.innerHTML='<div class="empty">Enter an input and press Convert.</div>';return}
if(!st.auto){h.innerHTML='<pre class="ast">'+esc(st.text)+'</pre>';return}
const lay=st.lay||st.auto;let P=pos.get(lay);if(!P){P=layout(lay);pos.set(lay,P)}if(needFit)fit(P,lay);h.innerHTML=drawSVG(st.auto,P,st.hl||{},$('#hd').checked)}
const hsl=i=>`background:hsl(${i*67%360} 70% 60%/.4)`;
function tableHTML(A){if(!A)return'<p class="mut">No automaton at this step.</p>';
if(A.type==='GNFA')return'<table id="tbl"><tr><th>From<th>Regex label<th>To</tr>'+A.transitions.map(t=>`<tr><td>${esc(lbl(A,t.from))}<td>${esc(t.symbol)}<td>${esc(lbl(A,t.to))}`).join('')+'</table>';
const al=[...A.alphabet];if(A.transitions.some(t=>t.symbol===EPS))al.push(EPS);const m=adjOf(A);
return'<table id="tbl"><tr><th>State'+al.map(a=>'<th>'+esc(a)).join('')+'</tr>'+A.states.map(s=>`<tr data-id="${s.id}"><td>${s.isStart?'→ ':''}${s.isAccept?'* ':''}${esc(s.label)}`+al.map(a=>'<td>'+(((m[s.id+'|'+a]||[]).map(y=>esc(lbl(A,y))).join(', '))||'–')).join('')).join('')+`</table><p class="mut">→ start · * accepting · ${A.states.length} states</p>`}
function simHTML(p){let h=`<div class="row"><input id="ss" placeholder="string, empty = ε" value="${esc(p.simStr||'')}" aria-label="Test string" style="flex:1"><button class="btn" id="run">Run</button></div>`;
if(p.simStr===undefined||!p.sims.length)return h+'<p class="mut">Run a string through every automaton of the pipeline; use Animate to watch active states glow on the canvas (all NFA states glow together).</p>';
p.sims.forEach((s,i)=>{const r=simulate(s.auto,p.simStr);s.r=r;h+=`<div class="exp" style="margin-bottom:8px"><b>${s.name}</b> (${s.auto.states.length} states) <span class="chip ${r.acc?'ok':'bad'}">${r.acc?'✔ ACCEPT':'✘ REJECT'}</span> <button class="btn gh" data-an="${i}">▶ Animate</button><div class="mut" style="word-break:break-word">${r.path.map(x=>F(x.map(id=>lbl(s.auto,id)).join(','))).join(' → ')}</div></div>`});return h}
function renderPanel(){const st=cur(),p=pg();$('#ptabs').innerHTML=PT.map(([k,n])=>`<button class="tb${k===ptab?' on':''}" data-pt="${k}">${n}</button>`).join('');let h='';
if(ptab==='sim')h=simHTML(p);else if(!st)h='<p class="mut">Nothing yet.</p>';
else if(ptab==='tbl')h=tableHTML(st.auto);
else if(ptab==='stp')h=`<div class="exp"><b>${esc(st.title)}</b><p>${esc(st.expl)}</p></div><ol class="sl">${steps().map((s,i)=>`<li><button data-go="${i}" class="${i===p.idx?'on':''}">${esc(s.title)}</button>`).join('')}</ol>`;
else if(ptab==='sub')h=tab==='r'&&p.sub?`<table><tr><th>DFA<th>NFA set`+p.sub.al.map(a=>`<th>${esc(a)}: move → closure → target`).join('')+'</tr>'+p.sub.rows.map(r=>`<tr data-id="${p.sub.rows.indexOf(r)}"><td><b>${r.name}</b><td>${F(r.set)}`+p.sub.al.map(a=>{const c=r.cells[a];return`<td>${F(c.mv)} → ${F(c.cl)} → <b>${c.tg||'∅'}</b>`}).join('')).join('')+'</table>':'<p class="mut">The subset table is available on the Regex → Automata page.</p>';
else if(ptab==='par')h=tab==='r'&&p.parts?p.parts.map((r,k)=>`<div style="margin-bottom:8px"><b>Round ${k}</b> <span class="mut">${esc(r.note)}</span><br>`+r.blocks.map((b,i)=>`<span class="blk" style="${hsl(i)}">{${esc(b.join(', '))}}</span>`).join('')+'</div>').join('')+`<p class="mut">Final: ${p.min.states.length} states (equal colour = merged).</p>`:'<p class="mut">Partition tables are available on the Regex → Automata page.</p>';
$('#pbody').innerHTML=h}
function renderPipe(){const p=pg();$('#pipe').innerHTML=p.stages.map((s,i)=>`<button class="ps${i===p.si?' on':''}" data-st="${i}"><b>${i+1}. ${s.name}</b><small>${s.badge||''}</small></button>`).join('<span class="ar">→</span>')}
function bar(){const n=steps().length,p=pg();$('#sc').textContent=n?`Step ${p.idx+1} / ${n}`:'';$('#pv').disabled=p.idx<=0;$('#nx').disabled=p.idx>=n-1}
function render(){if('rf'.includes(tab)){renderPipe();draw();renderPanel();bar()}}
function stop(){clearTimeout(timer);timer=null;$('#pl').textContent='▶ Play'}
function tick(){timer=setTimeout(()=>{const p=pg();if(p.idx<steps().length-1){p.idx++;render();tick()}else stop()},2300-$('#sp').value*200)}
function play(){if(timer)return stop();const p=pg();if(p.idx>=steps().length-1)p.idx=0;$('#pl').textContent='⏸ Pause';render();tick()}
function go(d){stop();const p=pg();p.idx=Math.max(0,Math.min(steps().length-1,p.idx+d));render()}
/* ---------- pipelines ---------- */
function runR(){const src=$('#rx').value.trim();let r;try{r=parse(src)}catch(e){return toast(`Position ${(e.pos??0)+1}: ${e.message}`,'bad')}
try{const ns=thompson(r.ast,r.alphabet),nfa=ns.at(-1).auto,sd=subset(nfa),mn=minimize(sd.dfa),p=pages.r,dn=mn.min.states.filter(s=>s.meta.dead).length;
Object.assign(p,{nfa,sub:sd,parts:mn.rounds,min:mn.min,dfa:sd.dfa,over:null,si:1,idx:ns.length-1,stages:[{name:'Parse',badge:`alphabet {${r.alphabet.join(',')}}`,steps:[{title:'Abstract syntax tree',expl:`Precedence: * + ? bind tightest, then concatenation, then union. Alphabet = {${r.alphabet.join(', ')}}.`,auto:null,text:astTxt(r.ast)}]},{name:'ε-NFA',badge:nfa.states.length+' states',steps:ns},{name:'DFA',badge:sd.dfa.states.length+' states',steps:sd.steps},{name:'Min DFA',badge:mn.min.states.length+' states'+(dn?' (incl. dead)':''),steps:mn.steps}],sims:[{name:'ε-NFA',auto:nfa,stage:1},{name:'DFA',auto:sd.dfa,stage:2},{name:'Min DFA',auto:mn.min,stage:3}]});
needFit=true;stop();render();toast(`ε-NFA ${nfa.states.length} → DFA ${sd.dfa.states.length} → min DFA ${mn.min.states.length} states`)}catch(e){toast(e.message,'bad')}}
function parseFA(t){const names=[],id=n=>{let i=names.indexOf(n);if(i<0){i=names.length;names.push(n)}return i};let start=null,acc=[];const tr=[];
t.split('\n').forEach((raw,ln)=>{const l=raw.replace(/#.*/,'').trim();if(!l)return;let m;
if(m=l.match(/^states?\s*:\s*(.*)$/i))m[1].split(/[\s,]+/).filter(Boolean).forEach(id);
else if(m=l.match(/^start\s*:\s*(\S+)$/i))start=id(m[1]);
else if(m=l.match(/^accept\s*:\s*(.*)$/i))acc=m[1].split(/[\s,]+/).filter(Boolean).map(id);
else{const w=l.split(/\s+/);if(w.length!==3)throw new E(`Line ${ln+1}: expected “from symbols to”`,0);w[1].split(',').forEach(s=>tr.push({from:id(w[0]),to:id(w[2]),symbol:/^(eps|ε)$/i.test(s)?EPS:s}))}});
if(start===null)throw new E('Missing “start: <state>” line',0);
return{type:'NFA',states:names.map((n,i)=>({id:i,label:n,isStart:i===start,isAccept:acc.includes(i)})),alphabet:[...new Set(tr.map(t=>t.symbol).filter(s=>s!==EPS))].sort(),transitions:tr}}
function runF(quiet){let A;try{A=parseFA($('#ft').value)}catch(e){return quiet||toast(e.message,'bad')}
try{const r=elim(A),p=pages.f;Object.assign(p,{over:null,si:1,idx:r.steps.length-1,sims:[{name:'Automaton',auto:A,stage:0}],stages:[{name:'Automaton',badge:A.states.length+' states',steps:[{title:'Your automaton',expl:'Parsed from the text editor. Press Eliminate to start state elimination.',auto:A,hl:{}}]},{name:'State elimination',badge:r.steps.length+' steps',steps:r.steps}]});
$('#fres').innerHTML=`<p>Regular expression: <code style="font-size:17px">${esc(r.regex)}</code> <button class="btn gh" id="cpy">Copy</button></p>`;needFit=true;stop();render();quiet||toast('Regex: '+r.regex)}catch(e){toast(e.message,'bad')}}
function toText(A){return`start: ${lbl(A,startId(A))}\naccept: ${A.states.filter(s=>s.isAccept).map(s=>s.label).join(' ')}\n`+A.transitions.map(t=>`${lbl(A,t.from)} ${t.symbol} ${lbl(A,t.to)}`).join('\n')}
/* ---------- UI wiring ---------- */
const EX=[['(a|b)*abb','Strings ending in abb. Expect 14 / 5 / 4 states. Try “aabb” then “abba” in the Simulator.'],['a*b*','All a’s then all b’s. Minimal DFA needs a dead state for “ba”.'],['(ab|a)*b','Words built from ab / a blocks, then b.'],['a+b?','At least one a, optional trailing b.'],['(0|1)*101','Binary strings ending in 101.'],['(a|)','Empty alternative = optional a; accepts ε and a.']];
$('#exs').innerHTML=EX.map((e,i)=>`<button class="ex" data-ex="${i}">${esc(e[0])}</button>`).join('');
function validate(){const c=$('#chip');try{const r=parse($('#rx').value);c.className='chip ok';c.textContent=`✔ Valid · alphabet {${r.alphabet.join(', ')}}`}catch(e){c.className='chip bad';c.textContent=`✘ Position ${(e.pos??0)+1}: ${e.message}`}}
const TABS=[['r','Regex → Automata'],['f','Automata → Regex'],['c','Compare'],['l','Learn']];
function setTab(t){tab=t;stop();needFit=true;document.querySelectorAll('.pg').forEach(x=>x.hidden=x.id!=='pg-'+t);const w='rf'.includes(t);$('#ws').hidden=$('#bar').hidden=$('#pipe').hidden=!w;$('#tabs').innerHTML=TABS.map(([k,n])=>`<button class="tb${k===t?' on':''}" data-tab="${k}">${n}</button>`).join('');render()}
function dl(name,blob){const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),2000)}
function svgStr(){const s=$('#cvh svg');if(!s)return null;const cs=getComputedStyle(document.documentElement);return new XMLSerializer().serializeToString(s).replace(/var\((--[\w-]+)\)/g,(_,v)=>cs.getPropertyValue(v).trim()).replace('<svg',`<svg width="1200" height="${Math.round(1200*vb.h/vb.w)}"`)}
function exp(k){const st=cur();if(!st)return;
if(k==='svg'){const x=svgStr();if(!x)return toast('Nothing to export','bad');dl('autolab.svg',new Blob([x],{type:'image/svg+xml'}));toast('SVG exported')}
else if(k==='png'){const x=svgStr();if(!x)return toast('Nothing to export','bad');const im=new Image;im.onload=()=>{const c=document.createElement('canvas');c.width=2400;c.height=Math.round(2400*vb.h/vb.w);const g=c.getContext('2d');g.fillStyle=getComputedStyle(document.body).backgroundColor;g.fillRect(0,0,c.width,c.height);g.drawImage(im,0,0,c.width,c.height);c.toBlob(b=>{dl('autolab.png',b);toast('PNG exported')})};im.onerror=()=>toast('PNG export failed','bad');im.src='data:image/svg+xml;charset=utf-8,'+encodeURIComponent(x)}
else if(k==='json'){if(!st.auto)return toast('No automaton at this step','bad');const{type,states,alphabet,transitions}=st.auto;dl('automaton.json',new Blob([JSON.stringify({type,states,alphabet,transitions},null,2)],{type:'application/json'}));toast('JSON saved')}
else{const t=$('#tbl');if(!t)return toast('Open the Table tab on an automaton step first','bad');dl('table.csv',new Blob([[...t.rows].map(r=>[...r.cells].map(c=>'"'+c.textContent.replace(/"/g,'""')+'"').join(',')).join('\n')],{type:'text/csv'}));toast('CSV exported')}}
document.addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;const d=b.dataset,p=pg(),id=b.id;
if(d.tab)return setTab(d.tab);
if(d.st!==undefined){stop();p.si=+d.st;p.over=null;p.idx=steps().length-1;needFit=true;return render()}
if(d.pt){ptab=d.pt;return renderPanel()}
if(d.go!==undefined){stop();p.idx=+d.go;return render()}
if(d.ex!==undefined){$('#rx').value=EX[d.ex][0];$('#exd').textContent='Experiment: '+EX[d.ex][1];validate();return runR()}
if(d.an!==undefined){const s=p.sims[+d.an],str=[...p.simStr||''];stop();p.si=s.stage;needFit=true;p.idx=0;p.over=s.r.path.map((set,k)=>({title:k?`Read “${str[k-1]}”`:'Start (ε-closure of start)',expl:`Active state(s): ${F(set.map(i=>lbl(s.auto,i)).join(', '))||'none'}.${k===s.r.path.length-1?` Input finished → ${s.r.acc?'ACCEPT':'REJECT'}.`:''}`,auto:s.auto,hl:{s:set}}));ptab='stp';render();return play()}
switch(id){case'go':return runR();case'gof':return runF();case'pv':return go(-1);case'nx':return go(1);case'pl':return play();
case'fit':needFit=true;return draw();case'rl':{const st=cur();if(st?.auto){pos.delete(st.lay||st.auto);needFit=true;draw()}return}
case'svg':case'png':case'json':case'csv':return exp(id);
case'th':{const r=document.documentElement,dark=r.dataset.theme?r.dataset.theme==='dark':matchMedia('(prefers-color-scheme:dark)').matches;r.dataset.theme=dark?'light':'dark';try{localStorage.setItem('al-th',r.dataset.theme)}catch(_){}return}
case'run':p.simStr=$('#ss').value;return renderPanel();
case'cpy':try{navigator.clipboard.writeText($('#fres code').textContent);toast('Copied')}catch(_){toast('Copy failed','bad')}return;
case'loadc':{const A=pages.r.dfa;if(!A)return toast('Convert a regex first','bad');$('#ft').value=toText(A);return runF()}
case'cmp':{try{const a=nfaOf($('#c1').value),b=nfaOf($('#c2').value),r=equiv(a,b);let h;
if(r.eq===true)h='<span class="chip ok">✔ Equivalent – both accept exactly the same language</span>';else if(r.eq===false){const w=r.w||EPS;h=`<span class="chip bad">✘ Not equivalent</span><p>Shortest distinguishing string: <code>${esc(w)}</code> – accepted only by ${simulate(a,r.w).acc?'regex 1':'regex 2'}.</p>`}else h='<span class="chip bad">Search limit reached</span>';
$('#cres').innerHTML=h+`<div class="g2" style="margin-top:12px"><div class="exp"><b>First strings of regex 1</b><p>${esc(enumerate(a).join(', '))}</p></div><div class="exp"><b>First strings of regex 2</b><p>${esc(enumerate(b).join(', '))}</p></div></div>`}catch(e){toast(`Position ${(e.pos??0)+1}: ${e.message}`,'bad')}return}}});
document.addEventListener('input',e=>{if(e.target.id==='rx')validate();if(e.target.id==='ss')pg().simStr=e.target.value;if(e.target.id==='hd'){needFit=true;draw()}});
document.addEventListener('keydown',e=>{const t=e.target.tagName,typing=t==='INPUT'||t==='TEXTAREA';
if(e.key==='Enter'&&e.target.id==='rx'){e.preventDefault();return runR()}if(e.key==='Enter'&&e.target.id==='ss'){pg().simStr=e.target.value;return renderPanel()}if(e.key==='Enter'&&(e.ctrlKey||e.metaKey)&&e.target.id==='ft')return runF();
if(typing||!'rf'.includes(tab))return;if(e.key==='ArrowRight')go(1);else if(e.key==='ArrowLeft')go(-1);else if(e.key===' '){e.preventDefault();play()}});
document.addEventListener('mouseover',e=>{const t=e.target.closest('[data-id]');document.querySelectorAll('.hv').forEach(x=>x.classList.remove('hv'));if(t)document.querySelectorAll(`[data-id="${t.dataset.id}"]`).forEach(x=>x.classList.add('hv'))});
let ftT;$('#ft').addEventListener('input',()=>{clearTimeout(ftT);ftT=setTimeout(()=>{if(tab==='f')runF(true)},500)});
const cv=$('#cvh');
cv.addEventListener('pointerdown',e=>{const svg=cv.querySelector('svg'),st=cur();if(!svg||!st?.auto)return;const nd=e.target.closest('.nd'),r=svg.getBoundingClientRect();drag={id:nd?+nd.dataset.id:null,x:e.clientX,y:e.clientY,k:vb.w/r.width,P:pos.get(st.lay||st.auto)}});
addEventListener('pointermove',e=>{if(!drag)return;const dx=(e.clientX-drag.x)*drag.k,dy=(e.clientY-drag.y)*drag.k;drag.x=e.clientX;drag.y=e.clientY;if(drag.id!==null){const p=drag.P[drag.id];p.x+=dx;p.y+=dy}else{vb.x-=dx;vb.y-=dy}draw()});
addEventListener('pointerup',()=>drag=null);
cv.addEventListener('wheel',e=>{const svg=cv.querySelector('svg');if(!svg)return;e.preventDefault();const r=svg.getBoundingClientRect(),f=e.deltaY>0?1.12:.89,mx=vb.x+(e.clientX-r.left)/r.width*vb.w,my=vb.y+(e.clientY-r.top)/r.height*vb.h;vb={x:mx-(mx-vb.x)*f,y:my-(my-vb.y)*f,w:vb.w*f,h:vb.h*f};draw()},{passive:false});
addEventListener('resize',()=>{needFit=true;draw()});
try{const t=localStorage.getItem('al-th');if(t)document.documentElement.dataset.theme=t}catch(_){}
validate();runR();runF(true);setTab('r');
