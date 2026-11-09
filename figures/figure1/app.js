'use strict';
const $=id=>document.getElementById(id), D=window.FIGURE1_DATA, engine=window.Figure1Engine;
const NS='http://www.w3.org/2000/svg', P=[0,.5,1.25,2.5,5], S=[1,5,10,25,50,100,200,400,800,1600], T=[1,2,4,8,16,32,64,128];
let mode='real', current=null, fullBox=null, viewBox=null, drag=null, updateTimer=null, generation=0, animation=null, compare=false;
const lookup=new Map(D.records.map(r=>[[r.game,r.sim,r.threads,r.puct].join(':'),r]));
function prettify(s){return s.split('_').map(x=>x[0].toUpperCase()+x.slice(1)).join(' ')}
const gameRecords=new Map(D.games.map(g=>[g,D.records.filter(r=>r.game===g).sort((a,b)=>a.sim-b.sim||a.threads-b.threads||a.puct-b.puct)]));
const rankedGames=[...D.games].sort((a,b)=>gameRecords.get(b).length-gameRecords.get(a).length||a.localeCompare(b));
rankedGames.forEach(g=>{const option=document.createElement('option');option.value=g;const count=gameRecords.get(g).length;const trees=gameRecords.get(g).reduce((sum,r)=>sum+(r.stepCount||1),0);option.textContent=prettify(g)+' · '+count+' settings / '+trees.toLocaleString()+' trees'+(count>=100?' (recommended)':'');$('game').append(option)});
rankedGames.filter(g=>gameRecords.get(g).length>=100).slice(0,2).forEach(g=>{const button=document.createElement('button');button.type='button';button.textContent=prettify(g)+' '+gameRecords.get(g).length+' settings';button.onclick=()=>{$('game').value=g;$('game').dispatchEvent(new Event('input'))};$('recommendedGames').append(button)});
let coverageGame='';
function selectSnapshot(record){$('simulation').value=S.indexOf(record.sim);$('threads').value=T.indexOf(record.threads);$('puct').value=P.indexOf(record.puct);$('searchStep').value=0}
function refreshCoverage(){const o=options(),records=gameRecords.get(o.game);if(coverageGame!==o.game){coverageGame=o.game;const sims=[...new Set(records.map(r=>r.sim))],threads=[...new Set(records.map(r=>r.threads))],pucts=[...new Set(records.map(r=>r.puct))];$('gameCoverage').textContent=`${records.length} recorded settings · ${records.reduce((sum,r)=>sum+(r.stepCount||1),0).toLocaleString()} trees · ${sims.length} simulation counts · ${threads.length} thread counts · ${pucts.length} coefficients`;$('snapshotPreset').replaceChildren();const placeholder=document.createElement('option');placeholder.value='';placeholder.textContent='Choose an archived setting';$('snapshotPreset').append(placeholder);for(const r of records){const option=document.createElement('option');option.value=[r.sim,r.threads,r.puct].join(':');option.textContent=`${r.sim} simulations · ${r.threads} threads · c=${r.puct}`;$('snapshotPreset').append(option)}$('simCoverage').replaceChildren();for(const n of sims.sort((a,b)=>a-b)){const chip=document.createElement('span');chip.textContent=`${n} simulations: ${records.filter(r=>r.sim===n).length} settings`;$('simCoverage').append(chip)}}$('snapshotPreset').value=[o.budget,o.threads,o.c].join(':');$('snapshotPreset').closest('.snapshot-picker').hidden=mode!=='real'}
$('snapshotPreset').onchange=()=>{if(!$('snapshotPreset').value)return;const [n,t,c]=$('snapshotPreset').value.split(':').map(Number);selectSnapshot({sim:n,threads:t,puct:c});schedule()};
$('game').addEventListener('input',()=>{const o=options();if(mode==='real'&&!lookup.has([o.game,o.budget,o.threads,o.c].join(':'))){const records=gameRecords.get(o.game);selectSnapshot(records.find(r=>r.sim===50&&r.threads===1&&r.puct===0)||records[0])}});
$('game').value='freeway';$('inventory').textContent=`${D.records.length} recorded settings · ${D.games.length} games`;
function options(){return {game:$('game').value,c:mode==='real'?P[+$('puct').value]:+$('puct').value,budget:S[+$('simulation').value],threads:T[+$('threads').value],seed:String($('seed').value||42),step:+$('searchStep').value,virtualLoss:$('virtualLoss').checked}}
function setMode(newMode){const before=options();mode=newMode;$('realMode').classList.toggle('active',mode==='real');$('modelMode').classList.toggle('active',mode==='model');$('modelOptions').hidden=mode==='real';$('puct').max=mode==='real'?4:5;$('puct').step=mode==='real'?1:.05;$('puct').value=mode==='real'?P.reduce((best,v,i)=>Math.abs(v-before.c)<Math.abs(P[best]-before.c)?i:best,0):before.c;$('simulation').max=mode==='real'?Math.max(...D.records.map(r=>S.indexOf(r.sim))):9;$('threads').max=mode==='real'?5:7;$('simulation').value=Math.min(+$('simulation').value,+$('simulation').max);$('threads').value=Math.min(+$('threads').value,+$('threads').max);$('modeDescription').textContent=mode==='real'?'Inspect archived trees from recorded experiments. Choose a search step within the first recorded episode.':'Compute an illustrative PUCT tree instantly. Use the same seed to compare parameter settings.';$('modeBadge').textContent=mode==='real'?'RAW EXPERIMENT':'ILLUSTRATIVE PUCT';schedule()}
function metrics(flat){const depths=[],counts=[],children=flat.map(()=>[]);flat.forEach((row,i)=>{depths[i]=row[0]<0?0:depths[row[0]]+1;if(row[0]>=0)children[row[0]].push(i);counts[depths[i]]=(counts[depths[i]]||0)+1});return {nodes:flat.length,depth:Math.max(...depths),leaves:children.filter(x=>!x.length).length,mean:depths.reduce((a,b)=>a+b,0)/flat.length,children,depths}}
function layout(flat){const stats=metrics(flat), leaves=Array(flat.length).fill(1),xs=Array(flat.length);for(let i=flat.length-1;i>=0;i--){if(stats.children[i].length)leaves[i]=stats.children[i].reduce((a,id)=>a+leaves[id],0);stats.children[i].sort((a,b)=>leaves[b]-leaves[a])}let cursor=0;function visit(i){if(!stats.children[i].length){xs[i]=cursor++;return}stats.children[i].forEach(visit);xs[i]=(xs[stats.children[i][0]]+xs[stats.children[i].at(-1)])/2}visit(0);const width=Math.max(230,Math.min(2400,(cursor-1)*12+60)),height=Math.max(140,stats.depth*16+70),space=cursor>1?(width-60)/(cursor-1):0;const positions=flat.map((_,i)=>[cursor>1?30+xs[i]*space:width/2,30+stats.depths[i]*16]);return {stats,positions,box:[0,0,width,height]}}
function make(tag,attrs){const el=document.createElementNS(NS,tag);for(const [key,value] of Object.entries(attrs))el.setAttribute(key,value);return el}
function draw(svg,flat,isMain=false){svg.replaceChildren();if(!flat?.length)return null;const L=layout(flat), edges=make('g',{fill:'none',stroke:'#273135','stroke-width':.9,opacity:.62}),nodes=make('g',{});flat.forEach((row,i)=>{const [x,y]=L.positions[i];if(row[0]>=0){const p=L.positions[row[0]];edges.append(make('line',{x1:p[0],y1:p[1],x2:x,y2:y}))}const radius=$('visits').checked?Math.min(5,1.3+Math.log2(1+row[2])*.45):1.8;const node=make('circle',{cx:x,cy:y,r:radius,fill:i===0?'#287799':'#17292e',opacity:row[2]>0?1:.45});node.dataset.node=String(i);if(isMain){node.addEventListener('pointerenter',e=>showTooltip(e,i,flat,L.stats));node.addEventListener('pointerleave',()=>{$('tooltip').hidden=true})}nodes.append(node)});svg.append(edges,nodes);svg.setAttribute('viewBox',L.box.join(' '));svg.setAttribute('preserveAspectRatio','xMidYMin meet');if(isMain){fullBox=L.box;viewBox=[...L.box]}return L.stats}
function showTooltip(e,i,flat,stats){const row=flat[i],box=$('treeCanvas').getBoundingClientRect(),tip=$('tooltip');tip.replaceChildren();['Node '+i+' · Depth '+stats.depths[i],'Action '+row[1]+' · Visits '+row[2],'Policy '+Number(row[4]).toFixed(4)+' · Q '+Number(row[5]).toFixed(4)].forEach(t=>{let d=document.createElement('div');d.textContent=t;tip.append(d)});tip.style.left=Math.min(Math.max(10,e.clientX-box.left+10),box.width-230)+'px';tip.style.top=Math.max(10,Math.min(e.clientY-box.top+10,box.height-105))+'px';tip.hidden=false}
function resetView(){if(fullBox){viewBox=[...fullBox];$('treeSvg').setAttribute('viewBox',viewBox.join(' '))}}
function schedule(){if(animation){clearInterval(animation);animation=null;$('play').textContent='Animate model search'}const o=options();$('puctValue').textContent=Number(o.c).toFixed(mode==='model'||o.c===1.25?2:1);$('simValue').textContent=o.budget.toLocaleString();$('threadValue').textContent=o.threads;clearTimeout(updateTimer);updateTimer=setTimeout(update,20)}
const chunkCache=new Map();
async function stepTree(record,step){
 if(step===0)return record.nodes;
 const chunk=record.stepChunks?.find(c=>step>=c.start&&step<=c.end);
 if(!chunk)throw Error('No archived tree for this step');
 const file=chunk.file.split('/').at(-1);
 if(!chunkCache.has(file)){
  const task=new Promise((resolve,reject)=>{
   const script=document.createElement('script');script.src=(record.stepBase&&chunk.start>=(record.localSteps||0)?record.stepBase:'')+chunk.file;
   script.onerror=()=>{script.remove();reject(Error('Step archive could not be loaded'))};
   script.onload=async()=>{try{
    const encoded=window.FIGURE1_STEP_CHUNKS[file];delete window.FIGURE1_STEP_CHUNKS[file];
    const bytes=Uint8Array.from(atob(encoded),c=>c.charCodeAt(0));
    const stream=new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'));
    const trees=JSON.parse(await new Response(stream).text());resolve(trees);
   }catch(e){reject(e)}finally{script.remove()}};
   document.head.append(script)
  });chunkCache.set(file,task);
  if(chunkCache.size>8)chunkCache.delete(chunkCache.keys().next().value);
 }
 return (await chunkCache.get(file))[step-chunk.start];
}
async function update(){
 const o=options();refreshCoverage();const token=++generation;let record;
 if(mode==='real'){
  record=lookup.get([o.game,o.budget,o.threads,o.c].join(':'));
  const steps=record?.stepCount||1;
  $('stepControl').hidden=false;$('searchStep').max=steps-1;
  $('searchStep').value=Math.min(o.step,steps-1);o.step=+$('searchStep').value;
  $('stepValue').textContent=o.step;$('stepEnd').textContent=`${steps.toLocaleString()} recorded steps`;
  $('searchStep').disabled=!record||steps===1;
  $('notice').textContent=record?'':`No recorded tree for ${o.budget} simulations, ${o.threads} threads, c=${o.c}. Choose an available setting.`;
  if(record){
   try{const nodes=await stepTree(record,o.step);if(token!==generation)return;record={...record,nodes,move:o.step}}
   catch(e){if(token!==generation)return;record=null;$('notice').textContent=e.message}
  }
 }else{
  $('stepControl').hidden=true;
  const result=engine.runTree(o);record={nodes:result.nodes,source:`Browser PUCT · seed=${o.seed} · virtual loss=${o.virtualLoss} · batches=${result.batches}`,move:0};
  $('notice').textContent=o.threads>o.budget?'Threads exceed the simulation count; the batch is capped by remaining simulations.':'';
 }
 if(token!==generation)return;
 current=record?{...record,options:o,mode}:null;$('empty').hidden=!!record;$('treeTitle').textContent=prettify(o.game)+(mode==='real'?` · step ${o.step}`:'');
 const stats=draw($('treeSvg'),record?.nodes,true);
 $('nodesStat').textContent=stats?.nodes.toLocaleString()??'—';$('depthStat').textContent=stats?.depth??'—';$('leavesStat').textContent=stats?.leaves.toLocaleString()??'—';$('meanStat').textContent=stats?stats.mean.toFixed(2):'—';
 $('provenance').textContent=record?`c=${o.c} · simulations=${o.budget} · threads=${o.threads} · ${mode==='real'?`episode 1, recorded search step ${o.step}`:'illustrative model'}. Source: ${record.source}`:'No recorded tree for this setting. Missing experiments are not interpolated.';
 $('export').disabled=!record;$('saveJson').disabled=!record;if(compare)renderCompare()
}
async function renderCompare(){
 const o=options(),container=$('compareGrid'),epoch=generation;container.replaceChildren();
 for(const t of [1,32])for(const c of [0,5]){
  const card=document.createElement('article');card.className='compare-card';const title=document.createElement('h4');title.textContent=`PUCT ${c.toFixed(1)} · threads ${t} · n=${o.budget}`;card.append(title);container.append(card);
  let r=mode==='real'?lookup.get([o.game,o.budget,t,c].join(':')):engine.runTree({...o,c,threads:t});
  if(r&&mode==='real'){
   const step=Math.min(o.step,(r.stepCount||1)-1);
   try{r={nodes:await stepTree(r,step)};title.textContent+=` · step ${step}`}catch(e){r=null}
  }
  if(epoch!==generation||!compare)return;
  if(r){const svg=make('svg',{'aria-label':title.textContent});card.append(svg);draw(svg,r.nodes)}
  else{const missing=document.createElement('div');missing.className='missing';missing.textContent='No recorded tree for this corner';card.append(missing)}
 }
}
function download(name,data,type){const blob=new Blob([data],{type}),url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),1000)}
$('realMode').onclick=()=>setMode('real');$('modelMode').onclick=()=>setMode('model');['puct','simulation','threads','game','seed','virtualLoss','visits','searchStep'].forEach(id=>$(id).addEventListener('input',schedule));$('reseed').onclick=()=>{$('seed').value=(+$('seed').value+1)%999999;schedule()};$('fit').onclick=resetView;$('compareToggle').onclick=()=>{compare=!compare;$('comparison').hidden=!compare;$('compareToggle').textContent=compare?'Hide comparison':'Compare corners';if(compare)renderCompare()};$('reset').onclick=()=>{$('game').value='freeway';$('simulation').value=4;$('threads').value=0;$('seed').value=42;$('searchStep').value=0;$('virtualLoss').checked=true;$('visits').checked=false;setMode('real');$('puct').value=0;schedule()};
$('export').onclick=()=>{if(!current)return;const clone=$('treeSvg').cloneNode(true);clone.setAttribute('xmlns',NS);clone.setAttribute('width','1200');clone.setAttribute('height','900');clone.setAttribute('viewBox',fullBox.join(' '));clone.querySelectorAll('[data-node]').forEach(n=>n.removeAttribute('data-node'));const metadata=make('metadata',{});metadata.textContent=JSON.stringify({mode:current.mode,options:current.options,source:current.source});clone.prepend(metadata);download(`figure1_${current.options.game}_c${current.options.c}_n${current.options.budget}_t${current.options.threads}_step${current.options.step}.svg`,new XMLSerializer().serializeToString(clone),'image/svg+xml')};$('saveJson').onclick=()=>{if(current)download('figure1_tree.json',JSON.stringify(current,null,2),'application/json')};
$('play').onclick=()=>{if(animation){clearInterval(animation);animation=null;$('play').textContent='Animate model search';return}if(mode!=='model')setMode('model');clearTimeout(updateTimer);const target=options().budget;let n=0;$('play').textContent='Stop animation';const o=options();animation=setInterval(()=>{n=Math.min(target,n+Math.max(1,Math.ceil(target/45)));const result=engine.runTree({...o,budget:n});current={nodes:result.nodes,options:{...o,budget:n},mode:'model',source:'Illustrative PUCT animation'};const stats=draw($('treeSvg'),result.nodes,true);$('nodesStat').textContent=stats.nodes;$('depthStat').textContent=stats.depth;$('leavesStat').textContent=stats.leaves;$('meanStat').textContent=stats.mean.toFixed(2);$('notice').textContent=`Search progress ${n}/${target}`;$('empty').hidden=true;$('provenance').textContent=`Illustrative PUCT animation · seed=${o.seed} · ${n}/${target} simulations`;$('export').disabled=false;$('saveJson').disabled=false;if(n===target){clearInterval(animation);animation=null;$('play').textContent='Animate model search';update()}},60)};
$('treeSvg').addEventListener('wheel',e=>{if(!viewBox)return;e.preventDefault();const factor=e.deltaY>0?1.12:.88;const w=Math.max(fullBox[2]/20,Math.min(fullBox[2]*4,viewBox[2]*factor)),h=w*fullBox[3]/fullBox[2];viewBox=[viewBox[0]+(viewBox[2]-w)/2,viewBox[1]+(viewBox[3]-h)/2,w,h];$('treeSvg').setAttribute('viewBox',viewBox.join(' '))},{passive:false});$('treeSvg').addEventListener('pointerdown',e=>{if(!viewBox||e.target.tagName==='circle')return;drag={x:e.clientX,y:e.clientY,box:[...viewBox]};$('treeSvg').setPointerCapture(e.pointerId);$('treeSvg').classList.add('dragging')});$('treeSvg').addEventListener('pointermove',e=>{if(!drag)return;const r=$('treeSvg').getBoundingClientRect(),scale=Math.max(drag.box[2]/r.width,drag.box[3]/r.height);viewBox=[drag.box[0]-(e.clientX-drag.x)*scale,drag.box[1]-(e.clientY-drag.y)*scale,drag.box[2],drag.box[3]];$('treeSvg').setAttribute('viewBox',viewBox.join(' '))});['pointerup','pointercancel'].forEach(type=>$('treeSvg').addEventListener(type,()=>{drag=null;$('treeSvg').classList.remove('dragging')}));
setMode('real');
