// AutoLab algorithm layer: pure logic, no DOM access.
export const EPS='ε';
class E extends Error{constructor(m,p){super(m);this.pos=p}}
/* ---------- parser ---------- */
function parse(src){let i=0;const s=src,al=new Set();if(!s.trim())throw new E('Enter a regular expression',0);
const alt=()=>{let l=cat();while(s[i]==='|'){i++;l={t:'alt',a:l,b:cat()}}return l},
cat=()=>{let l=null;while(i<s.length&&s[i]!=='|'&&s[i]!==')'){const r=post();l=l?{t:'cat',a:l,b:r}:r}return l||{t:'eps'}},
post=()=>{let a=atom();while(i<s.length&&'*+?'.includes(s[i])){a={t:{'*':'star','+':'plus','?':'opt'}[s[i]],a};i++}return a},
lit=c=>(al.add(c),{t:'lit',c}),
atom=()=>{const c=s[i];
if(c==='('){const o=i++,r=alt();if(s[i]!==')')throw new E('Unmatched “(” opened here',o);i++;return r}
if('*+?'.includes(c))throw new E(`Nothing to repeat before “${c}”`,i);
if('{}^$'.includes(c))throw new E(`“${c}” is not supported (anchors and counted repetition are outside this tool)`,i);
if(c==='\\'){const d=s[i+1];if(d===undefined)throw new E('Dangling escape',i);if(/[0-9bBdDwWsS]/.test(d))throw new E(`“\\${d}” (back-reference / shorthand) is not supported`,i);i+=2;return lit(d)}
if(c==='['){const o=i++,cs=[];while(i<s.length&&s[i]!==']'){const x=s[i++];if(s[i]==='-'&&i+1<s.length&&s[i+1]!==']'){const y=s[i+1];i+=2;for(let k=x.charCodeAt(0);k<=y.charCodeAt(0);k++)cs.push(String.fromCharCode(k))}else cs.push(x)}
if(s[i]!==']')throw new E('Unclosed “[”',o);i++;if(!cs.length)throw new E('Empty character class',o);return cs.map(lit).reduce((a,b)=>({t:'alt',a,b}))}
i++;return c===EPS?{t:'eps'}:lit(c)};
const ast=alt();if(i<s.length)throw new E('Unmatched “)”',i);return{ast,alphabet:[...al].sort()}}
const astTxt=(n,d=0)=>'  '.repeat(d)+({lit:'LITERAL '+n.c,eps:'ε (EPSILON)',cat:'CONCAT',alt:'UNION',star:'STAR  *',plus:'PLUS  +',opt:'OPTIONAL  ?'}[n.t])+'\n'+[n.a,n.b].filter(Boolean).map(x=>astTxt(x,d+1)).join('');
/* ---------- automaton helpers ---------- */
const M=new WeakMap,adjOf=A=>{let m=M.get(A);if(!m){m={};A.transitions.forEach(t=>(m[t.from+'|'+t.symbol]??=[]).push(t.to));M.set(A,m)}return m},
startId=A=>A.states.find(s=>s.isStart).id,key=s=>[...s].sort((a,b)=>a-b).join(','),F=k=>'{'+k+'}',
move=(A,set,a)=>{const m=adjOf(A),r=new Set;set.forEach(x=>(m[x+'|'+a]||[]).forEach(y=>r.add(y)));return r},
clo=(A,set)=>{const m=adjOf(A),st=[...set],seen=new Set(set);while(st.length){const x=st.pop();(m[x+'|'+EPS]||[]).forEach(y=>{if(!seen.has(y)){seen.add(y);st.push(y)}})}return seen},
lbl=(A,id)=>A.states.find(s=>s.id===id)?.label??id,accepts=(A,set)=>A.states.some(s=>s.isAccept&&set.has(s.id));
/* ---------- Thompson ---------- */
function thompson(ast,al){let n=0;const tr=[],steps=[],ed=(f,t,s)=>tr.push({from:f,to:t,symbol:s}),ns=()=>n++;
const go=a=>{const l=a.a&&go(a.a),r=a.b&&go(a.b),n0=n,t0=tr.length;let f,ex,ti;
if(a.t==='lit'||a.t==='eps'){const s=ns(),e=ns();ed(s,e,a.t==='lit'?a.c:EPS);f={s,e};ti=a.t==='lit'?`Literal “${a.c}”`:'Epsilon';ex=`New start ${s} and accept ${e} joined by an edge labelled ${a.t==='lit'?a.c:EPS}.`}
else if(a.t==='cat'){ed(l.e,r.s,EPS);f={s:l.s,e:r.e};ti='Concatenation';ex=`ε-edge from accept ${l.e} of the left fragment to start ${r.s} of the right fragment.`}
else if(a.t==='alt'){const s=ns(),e=ns();ed(s,l.s,EPS);ed(s,r.s,EPS);ed(l.e,e,EPS);ed(r.e,e,EPS);f={s,e};ti='Union (|)';ex=`New start ${s} branches by ε into both fragments; both accepts lead by ε to new accept ${e}.`}
else{const c=l||go(a.a);const s=ns(),e=ns();ed(s,c.s,EPS);ed(c.e,e,EPS);if(a.t!=='plus')ed(s,e,EPS);if(a.t!=='opt')ed(c.e,c.s,EPS);f={s,e};ti={star:'Kleene star (*)',plus:'Plus (+)',opt:'Optional (?)'}[a.t];ex=`New start ${s} and accept ${e}; ε entry and exit edges${a.t!=='plus'?', ε skip edge (zero repeats)':''}${a.t!=='opt'?', ε loop-back edge (repeat)':''}.`}
const st=[];for(let k=0;k<n;k++)st.push({id:k,label:''+k,isStart:k===f.s,isAccept:k===f.e});
steps.push({title:ti,expl:ex,auto:{type:'NFA',states:st,alphabet:al,transitions:tr.map(t=>({...t}))},hl:{s:Array.from({length:n-n0},(_,k)=>n0+k),e:tr.slice(t0).map(t=>t.from+'>'+t.to)}});return f};
go(ast);const fin=steps.at(-1).auto;steps.forEach(s=>s.lay=fin);steps.at(-1).expl+=` Done: ε-NFA with ${fin.states.length} states.`;return steps}
/* ---------- subset construction ---------- */
function subset(N,lim=200){const al=N.alphabet,acc=new Set(N.states.filter(s=>s.isAccept).map(s=>s.id)),nm=i=>i<26?String.fromCharCode(65+i):'S'+i,
q0=clo(N,[startId(N)]),ds=[q0],idx={[key(q0)]:0},tr=[],rows=[],steps=[],
build=()=>({type:'DFA',states:ds.map((s,i)=>({id:i,label:nm(i),isStart:i===0,isAccept:[...s].some(x=>acc.has(x)),meta:{set:F(key(s))}})),alphabet:al,transitions:tr.map(t=>({...t}))});
steps.push({title:'Start state',expl:`ε-closure of the NFA start state ${startId(N)} is ${F(key(q0))}; it becomes DFA state A.`,auto:build(),hl:{s:[0]}});
for(let i=0;i<ds.length;i++){const cells={},note=[],nw=[],t0=tr.length;
al.forEach(a=>{const mv=move(N,ds[i],a),c=clo(N,mv);let tg=null;
if(c.size){const k=key(c);if(!(k in idx)){if(ds.length>=lim)throw new E(`More than ${lim} DFA states – stopped to avoid exponential blow-up`,0);idx[k]=ds.length;ds.push(c);nw.push(ds.length-1)}tg=idx[k];tr.push({from:i,to:tg,symbol:a})}
cells[a]={mv:key(mv),cl:key(c),tg:tg===null?null:nm(tg)};note.push(`on “${a}”: move = ${F(key(mv))}, ε-closure = ${F(key(c))} → ${tg===null?'no transition':(nw.includes(tg)?'new state ':'state ')+nm(tg)}`)});
rows.push({name:nm(i),set:key(ds[i]),cells});
steps.push({title:`Process state ${nm(i)}`,expl:`State ${nm(i)} = ${F(key(ds[i]))}. `+note.join('; ')+'.',auto:build(),hl:{s:[i,...nw],e:tr.slice(t0).map(t=>t.from+'>'+t.to)}})}
const dfa=build();steps.forEach(s=>s.lay=dfa);steps.at(-1).expl+=` All states processed: DFA has ${dfa.states.length} states.`;return{dfa,steps,rows,al}}
/* ---------- minimization ---------- */
function minimize(D){const al=D.alphabet,m=adjOf(D),s0=startId(D),acc=new Set(D.states.filter(s=>s.isAccept).map(s=>s.id)),L=Object.fromEntries(D.states.map(s=>[s.id,s.label]));L[-1]='dead';
const T=(x,a)=>x===-1?-1:((m[x+'|'+a]||[])[0]??-1),ids=[s0],seen=new Set(ids);
for(let k=0;k<ids.length;k++)al.forEach(a=>{const y=T(ids[k],a);if(y!==-1&&!seen.has(y)){seen.add(y);ids.push(y)}});
const removed=D.states.length-ids.length,addDead=ids.some(x=>al.some(a=>T(x,a)===-1));if(addDead)ids.push(-1);
const C={type:'DFA',states:ids.map(x=>({id:x,label:L[x],isStart:x===s0,isAccept:acc.has(x),meta:x===-1?{dead:true}:{set:D.states.find(s=>s.id===x).meta?.set}})),alphabet:al,transitions:ids.flatMap(x=>al.map(a=>({from:x,to:T(x,a),symbol:a})))};
const grp=b=>{const g={};ids.forEach(x=>(g[b[x]]??=[]).push(x));return Object.values(g)};
let blk={};ids.forEach(x=>blk[x]=acc.has(x)?1:0);
const rounds=[{blocks:grp(blk).map(g=>g.map(x=>L[x])),note:'Round 0: accepting vs non-accepting states.'}],
steps=[{title:'Round 0 – initial partition',expl:`Start with {accepting} and {non-accepting}.${removed?` ${removed} unreachable state(s) removed.`:''}${addDead?' A dead (trap) state was added so every state has a move on every symbol; it absorbs all missing transitions and is never accepting.':''}`,auto:C,lay:C,hl:{col:{...blk}}}];
for(let r=1;;r++){const sig={},nb={};let c=0;ids.forEach(x=>{const k=blk[x]+'|'+al.map(a=>blk[T(x,a)]).join(',');if(!(k in sig))sig[k]=c++;nb[x]=sig[k]});
if(c===new Set(Object.values(blk)).size)break;
const why=[];grp(blk).forEach(g=>{if(new Set(g.map(x=>nb[x])).size>1){const a=al.find(a=>new Set(g.map(x=>blk[T(x,a)])).size>1);why.push(`{${g.map(x=>L[x])}} splits on “${a}”: `+[...new Set(g.map(x=>blk[T(x,a)]))].map(b=>g.filter(x=>blk[T(x,a)]===b).map(x=>L[x])+' → block '+b).join(' vs '))}});
blk=nb;const txt=why.join('; ');rounds.push({blocks:grp(blk).map(g=>g.map(x=>L[x])),note:`Round ${r}: `+txt});steps.push({title:`Round ${r} – refine`,expl:txt+'.',auto:C,lay:C,hl:{col:{...blk}}})}
const bl=grp(blk),bi={};bl.forEach((g,i)=>g.forEach(x=>bi[x]=i));const order=[...new Set(ids.map(x=>bi[x]))],ren={};order.forEach((b,i)=>ren[b]=i);
const states=order.map((b,i)=>{const g=bl[b];return{id:i,label:'Q'+i,isStart:g.includes(s0),isAccept:acc.has(g[0]),meta:{members:F(g.map(x=>L[x])),dead:g.every(x=>!acc.has(x))&&!g.includes(s0)&&g.every(x=>al.every(a=>bi[T(x,a)]===b))}}}),
transitions=order.flatMap((b,i)=>al.map(a=>({from:i,to:ren[bi[T(bl[b][0],a)]],symbol:a}))),min={type:'DFA',states,alphabet:al,transitions},nd=states.filter(s=>s.meta.dead).length;
steps.push({title:'Merge equivalent states',expl:`The partition is stable. Each block becomes one state: ${states.length} states${nd?` (${states.length-nd} without the dead state – tick “hide dead state”)`:''}. Equal colours = merged states.`,auto:min,lay:min,hl:{col:Object.fromEntries(states.map(s=>[s.id,s.id]))}});
return{min,steps,rounds}}
/* ---------- regex algebra + state elimination ---------- */
const wr=(x,m)=>x.p>=m?x.s:'('+x.s+')',isE=x=>x&&x.s===EPS;
function U(a,b){if(!a)return b;if(!b)return a;if(a.s===b.s)return a;if(isE(b))[a,b]=[b,a];if(isE(a)){if(b.p===2&&/[*?]$/.test(b.s))return b;return{s:wr(b,2)+'?',p:2}}return{s:a.s+'|'+b.s,p:0}}
const C_=(a,b)=>!a||!b?null:isE(a)?b:isE(b)?a:{s:wr(a,1)+wr(b,1),p:1},
S_=a=>{if(!a||isE(a))return{s:EPS,p:2};if(a.p===2&&a.s.endsWith('*'))return a;if(a.p===2&&a.s.endsWith('?'))return{s:a.s.slice(0,-1)+'*',p:2};return{s:wr(a,2)+'*',p:2}};
function elim(A){const n=A.states.length,ix={};A.states.forEach((s,i)=>ix[s.id]=i);const S=n,Fn=n+1,R=Array.from({length:n+2},()=>Array(n+2).fill(null)),steps=[],
sym=c=>({s:c===EPS?EPS:(/[|()*+?\\\[\]{}]/.test(c)?'\\'+c:c),p:2}),add=(i,j,r)=>R[i][j]=U(R[i][j],r),name=i=>i===S?'S':i===Fn?'F':A.states[i].label,alive=new Set([...Array(n+2).keys()]);
A.transitions.forEach(t=>add(ix[t.from],ix[t.to],sym(t.symbol)));A.states.forEach(s=>{if(s.isStart)add(S,ix[s.id],sym(EPS));if(s.isAccept)add(ix[s.id],Fn,sym(EPS))});
const snap=(title,expl,q)=>{const ids=[...alive],tr=[];ids.forEach(i=>ids.forEach(j=>{if(R[i][j])tr.push({from:i,to:j,symbol:R[i][j].s})}));steps.push({title,expl,auto:{type:'GNFA',states:ids.map(i=>({id:i,label:name(i),isStart:i===S,isAccept:i===Fn})),alphabet:[],transitions:tr},hl:{r:q==null?[]:[q]}})};
snap('Initial GNFA','Added a new start S (ε to the old start) and a new accept F (ε from every accepting state). Parallel edges are merged with union “|”. Edge labels are now regular expressions.');
let rest=[...Array(n).keys()];
while(rest.length){const cost=q=>{let i=0,o=0;alive.forEach(p=>{if(p!==q){if(R[p][q])i++;if(R[q][p])o++}});return i*o};rest.sort((a,b)=>cost(a)-cost(b));const q=rest.shift(),lp=R[q][q];
snap(`Eliminate ${name(q)}`,`Removing ${name(q)} (cheapest: ${cost(q)} bypass edge pair(s)). For each p→${name(q)}→r the new label is R(p,r) | R(p,${name(q)}) ${name(q)}-loop* R(${name(q)},r)${lp?`; loop here is ${lp.s}`:''}.`,q);
alive.delete(q);const l=S_(lp);[...alive].forEach(p=>[...alive].forEach(r=>{if(R[p][q]&&R[q][r])R[p][r]=U(R[p][r],C_(C_(R[p][q],l),R[q][r]))}))}
const res=R[S][Fn];snap('Result',`The single S→F edge is the answer: ${res?res.s:'∅ (empty language)'}.`);steps.forEach(s=>s.lay=steps[0].auto);return{steps,regex:res?res.s:'∅'}}
/* ---------- simulate / equivalence / enumerate ---------- */
function simulate(A,str){let cur=clo(A,[startId(A)]);const path=[[...cur]];for(const ch of str){cur=clo(A,move(A,cur,ch));path.push([...cur])}return{acc:accepts(A,cur),path}}
function equiv(A,B){const al=[...new Set([...A.alphabet,...B.alphabet])].sort(),sa=clo(A,[startId(A)]),sb=clo(B,[startId(B)]),seen=new Set([key(sa)+'#'+key(sb)]),q=[[sa,sb,'']];
for(let i=0;i<q.length;i++){const[x,y,w]=q[i];if(accepts(A,x)!==accepts(B,y))return{eq:false,w};if(seen.size>60000)return{eq:null};
for(const a of al){const nx=clo(A,move(A,x,a)),ny=clo(B,move(B,y,a)),k=key(nx)+'#'+key(ny);if(!seen.has(k)){seen.add(k);q.push([nx,ny,w+a])}}}return{eq:true}}
function enumerate(N,n=12){const out=[],q=[[clo(N,[startId(N)]),'']];for(let i=0;i<q.length&&out.length<n&&i<20000;i++){const[s,w]=q[i];if(accepts(N,s))out.push(w||EPS);N.alphabet.forEach(a=>{const t=clo(N,move(N,s,a));if(t.size)q.push([t,w+a])})}return out}
const nfaOf=src=>{const r=parse(src.trim());return thompson(r.ast,r.alphabet).at(-1).auto};

export {E,parse,astTxt,thompson,subset,minimize,elim,simulate,equiv,enumerate,nfaOf,startId,key,F,move,clo,lbl,accepts,adjOf};
