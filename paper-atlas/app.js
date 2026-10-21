/* Spatial Atlas — all reading data is served from this site's own origin. */
'use strict';
const CATEGORIES = [
  {id:'', label:'全部论文', icon:'▤'},
  {id:'visual-localization',label:'视觉定位',icon:'◎'},
  {id:'point-localization',label:'点云定位',icon:'⌖'},
  {id:'place-recognition',label:'位置识别',icon:'◈'},
  {id:'registration',label:'点云配准',icon:'⊞'},
  {id:'point-processing',label:'点云处理',icon:'⠿'},
  {id:'uav-navigation',label:'无人机定位导航',icon:'⌁'}
];
const CATEGORY_NAMES = Object.fromEntries(CATEGORIES.map(c=>[c.id,c.label]));
const $ = s => document.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function safeUrl(u) { try {const url=new URL(u); return ['https:','http:'].includes(url.protocol)?url.href:'';} catch {return '';} }
function link(url,text,cls='') {const href=safeUrl(url);return href?`<a class="${cls}" href="${esc(href)}" target="_blank" rel="noopener noreferrer">${text}</a>`:'';}
function stored(key,fallback){try{return JSON.parse(localStorage.getItem(key))??fallback;}catch{return fallback;}}
let saved = new Set(stored('spatial-atlas:saved',[]));
const state = {view:'papers',category:'',year:'',venue:'',search:'',status:'',published:false,summary:false,sort:'newest',page:1};
let papers=[],preprints=[],meta={},sources=[],filtered=[],toastTimer;
const PAGE_SIZE=15;
function allPapers(){return [...papers,...preprints.filter(p=>!papers.some(q=>q.id===p.id))];}
function readingPool(){return state.view==='preprints'?preprints:state.view==='saved'?allPapers():papers;}
function persist(key,value){try{localStorage.setItem(key,JSON.stringify(value));return true;}catch{return false;}}
const preferredTheme=stored('spatial-atlas:theme','light');
document.documentElement.dataset.theme=preferredTheme;
function notify(message){$('#toast').textContent=message;$('#toast').classList.add('visible');clearTimeout(toastTimer);toastTimer=setTimeout(()=>$('#toast').classList.remove('visible'),2800);}
function dateText(value){if(!value)return '尚无成功记录';return String(value).slice(0,10);}
function hasSummary(p){return !!p.summary_zh?.trim();}
function venueLabel(p){const year=p.publication_status==='accepted'?p.accepted_year:p.year;return `${p.venue||'未标明出处'}${year?' '+year:''}`;}
function acceptedDateLabel(p){return p.publication_date_basis==='official-program-page-date'?'目录登记日期':p.publication_date_basis==='accepted-conference-edition-only'?'录用届次':'预印本公开日期';}
function publicationLabel(p){return {published:'正式发表',accepted:'已录用 / 待出版',preprint:'预印本'}[p.publication_status]||'预印本';}
function officialAcceptanceLabel(p){return String(p.venue_track||'').includes('待核验')?'官方目录收录':'官方录用确认';}
function publicationBadge(p){return `<span class="badge ${['published','accepted'].includes(p.publication_status)?p.publication_status:'preprint'}">${publicationLabel(p)}</span>${p.publication_status==='accepted'?`<span class="badge neutral">${p.acceptance_basis==='official'?officialAcceptanceLabel(p):'作者声明录用'}</span>`:''}`;}
function acceptanceDetails(p){
 if(p.publication_status!=='accepted')return '';
 const evidence=Array.isArray(p.acceptance_evidence)?p.acceptance_evidence:[];
 return `<div class="acceptance-panel"><h3>录用信息</h3><p>${esc(p.acceptance_note||'已找到录用信息，正式出版记录仍待核验。')}</p><p>证据类型：${p.acceptance_basis==='official'?(String(p.venue_track||'').includes('待核验')?'官方目录已列入，具体录用轨道待核验':'会议或出版方官方确认'):'作者公开声明，尚未获会议或出版方独立确认'}</p>${evidence.map(e=>`<p>${link(e.url,'查看录用证据 ↗')}${e.quote?`<br><q>${esc(e.quote)}</q>`:''}</p>`).join('')}</div>`;
}
function paperAuthors(p){return Array.isArray(p.authors)?p.authors.map(a=>typeof a==='string'?a:(a.name||'')).filter(Boolean):[];}
function updateCounts(){
  $('#tab-total').textContent=papers.length.toLocaleString();
  $('#preprint-total').textContent=preprints.length;
  $('#saved-total').textContent=allPapers().filter(p=>saved.has(p.id)).length;
  const pool=readingPool();const stats=[pool.length,6,new Set(pool.map(p=>p.venue).filter(Boolean)).size,pool.filter(hasSummary).length];
  document.querySelectorAll('#stats b').forEach((el,i)=>el.textContent=stats[i].toLocaleString());
  $('#category-nav').innerHTML=CATEGORIES.map(c=>`<button class="category-button ${state.category===c.id?'active':''}" data-category="${c.id}" aria-pressed="${state.category===c.id}"><span class="cat-icon">${c.icon}</span><span>${c.label}</span><span class="category-count">${pool.filter(p=>!c.id||p.categories.includes(c.id)).length}</span></button>`).join('');
  const years=[...new Set(pool.flatMap(p=>[p.year,...(p.publication_status==='accepted'&&p.accepted_year?[p.accepted_year]:[])]))].filter(Boolean).sort((a,b)=>b-a);
  $('#year-filter').innerHTML='<option value="">全部年份</option>'+years.map(y=>`<option value="${y}">${y} 年</option>`).join('');
  $('#year-options').innerHTML=[{value:'',label:'全部'},...years.map(y=>({value:String(y),label:y}))].map(y=>`<button class="year-button ${state.year===y.value?'active':''}" data-year="${esc(y.value)}" aria-pressed="${state.year===y.value}">${y.label}</button>`).join('');
}
function populateVenues(){
 const counts={};readingPool().forEach(p=>counts[p.venue]=(counts[p.venue]||0)+1);
 if(state.venue&&!counts[state.venue])counts[state.venue]=0;
 $('#venue-filter').innerHTML='<option value="">全部会议 / 期刊</option>'+Object.keys(counts).sort().map(v=>`<option value="${esc(v)}">${esc(v)} (${counts[v]})</option>`).join('');
 const groups={'#focus-cv':['TPAMI','IJCV','CVPR','ICCV','ECCV','NeurIPS','AAAI','ICML','ICLR','TIP'],'#focus-robotics':['TRO','IJRR','ICRA','IROS','RA-L','RSS']};
 for(const [selector,venues] of Object.entries(groups))$(selector).innerHTML=venues.map(v=>`<button class="venue-tag" data-venue="${v}" title="筛选 ${v}">${v}</button>`).join('');
}
function scheduleText(){return (Array.isArray(meta.schedule?.daily_times)&&meta.schedule.daily_times.length?meta.schedule.daily_times:[meta.schedule?.daily_at||'08:00']).join('、');}
function renderStatus(){
 const statusMap={ok:'本轮采集完成',partial:'持续补录中',curated_only:'已核验首批索引',error:'采集异常，保留旧索引'};
 const delayed=isUpdateDelayed();
 $('#update-status').textContent=delayed?'更新延迟，保留旧资料':statusMap[meta.collection_status]||'首批索引已就绪';
 $('#update-indicator').classList.toggle('ok',!delayed&&meta.collection_status==='ok');
 $('#last-updated').textContent=dateText(meta.generated_at);
 $('#schedule-status').textContent=meta.schedule?.configured?`每日 ${scheduleText()} (北京时间)`:'尚未启用';
}
function isUpdateDelayed(){
 const generated=Date.parse(meta.generated_at||'');
 return !!meta.schedule?.configured&&Number.isFinite(generated)&&Date.now()-generated>26*60*60*1000;
}
function applyFilters(){
 const tokens=state.search.toLocaleLowerCase().trim().split(/\s+/).filter(Boolean);
 filtered=readingPool().filter(p=>{
  if(state.view==='saved'&&!saved.has(p.id))return false;
  if(state.category&&!p.categories.includes(state.category))return false;
  if(state.year&&String(p.year)!==state.year&&!(p.publication_status==='accepted'&&String(p.accepted_year)===state.year))return false;
  if(state.venue&&p.venue!==state.venue)return false;
  if(state.status&&p.publication_status!==state.status)return false;
  if(state.published&&p.publication_status!=='published')return false;
  if(state.summary&&!hasSummary(p))return false;
  if(tokens.length){const text=[p.title,...paperAuthors(p),p.venue,p.accepted_year,publicationLabel(p),p.summary_zh,p.abstract,p.doi,p.arxiv_id,...p.categories.map(c=>CATEGORY_NAMES[c])].join(' ').toLocaleLowerCase();if(!tokens.every(t=>text.includes(t)))return false;}
  return true;
 });
 filtered.sort((a,b)=>state.sort==='title'?a.title.localeCompare(b.title):state.sort==='venue'?(a.venue.localeCompare(b.venue)||a.title.localeCompare(b.title)):state.sort==='oldest'?String(a.published||a.year).localeCompare(String(b.published||b.year)):String(b.published||b.year).localeCompare(String(a.published||a.year))||a.title.localeCompare(b.title));
 state.page=Math.min(state.page,Math.max(1,Math.ceil(filtered.length/PAGE_SIZE)));
}
function card(p){
 const isSaved=saved.has(p.id), authors=paperAuthors(p);
 const authorsShort=authors.length>5?authors.slice(0,5).join(', ')+` 等 ${authors.length} 位作者`:authors.join(', ');
 return `<article class="paper-card"><div class="paper-head"><div class="paper-meta"><span class="venue-badge">${esc(venueLabel(p))}</span>${publicationBadge(p)}${p.review_status==='pending'?'<span class="badge neutral">待审核</span>':''}<span class="paper-year">${p.publication_status==='accepted'?acceptedDateLabel(p)+' ':''}${esc(p.published||p.year)}</span></div><button class="bookmark-button" data-save="${esc(p.id)}" aria-pressed="${isSaved}" aria-label="${isSaved?'取消收藏':'收藏'}：${esc(p.title)}">${isSaved?'★':'☆'}</button></div><h3 class="paper-title"><button data-paper="${esc(p.id)}">${esc(p.title)}</button></h3><p class="paper-authors" title="${esc(authors.join(', '))}">${esc(authorsShort||'作者信息待补录')}</p>${hasSummary(p)?`<p class="paper-summary"><span class="summary-label">中文导读${p.summary_status==='generated'?' · AI':''}</span>${esc(p.summary_zh)}</p>`:'<p class="summary-pending">中文导读待补充，可先阅读原文摘要与官方论文。</p>'}<div class="paper-bottom"><div class="topic-tags">${p.categories.map(c=>`<button class="topic-tag" data-category="${esc(c)}">${esc(CATEGORY_NAMES[c]||c)}</button>`).join('')}</div><div class="paper-links">${link(p.source_url,'原文 ↗')}${link(p.pdf_url,'PDF ↗')}${link(p.code_url,'代码 ↗')}<button class="text-button" data-cite="${esc(p.id)}">引用</button></div></div></article>`;
}
function renderPapers(){
 populateVenues();updateCounts();applyFilters();
 $('#view-title').textContent=state.view==='saved'?'留给下一次深入阅读。':state.view==='preprints'?'预印本，先看方法与证据。':state.category?CATEGORY_NAMES[state.category]:'读懂空间，追踪前沿。';
 $('#view-description').textContent=state.view==='saved'?'收藏保存在当前浏览器，你可以随时导出引用。':state.view==='preprints'?'近期公开的相关候选，尚未完成质量审核，与精选论文库分开展示。':state.category?'聚焦一个方向，沿着方法与问题继续探索。':'跨越视觉与几何，从一篇论文开始。';
 $('#stats div:first-child span').textContent=state.view==='preprints'?'候选预印本':'已收录论文';
 $('#results-label').textContent=`${filtered.length.toLocaleString()} 篇论文`;
 const active=state.category||state.year||state.venue||state.search||state.status||state.published||state.summary;
 $('#clear-filters').hidden=!active;
 const chips=[['category',CATEGORY_NAMES[state.category]],['year',state.year],['venue',state.venue],['status',state.status?publicationLabel({publication_status:state.status}):''],['summary',state.summary?'已有中文导读':'']].filter(([k,v])=>v&&(k!=='category'||state.category));
 $('#active-filters').innerHTML=chips.map(([k,v])=>`<button class="filter-chip" data-clear="${k}">${esc(v)} ×</button>`).join('');
 $('#paper-list').innerHTML=filtered.length?filtered.slice((state.page-1)*PAGE_SIZE,state.page*PAGE_SIZE).map(card).join(''):`<div class="empty-state"><span class="empty-icon">${state.view==='saved'?'☆':'⌕'}</span><h3>${state.view==='saved'&&!active?'把感兴趣的论文留在这里':'没有找到匹配的论文'}</h3><p>${state.view==='saved'&&!active?'点击论文右上角的星标即可收藏。收藏仅保存在当前浏览器。':'可以尝试缩短关键词或清除筛选。暂无结果也可能表示这一来源尚在补录，详见来源与更新。'}</p><button class="button" ${active?'data-reset':'data-view="papers"'}>${active?'清除筛选':'浏览论文库'}</button></div>`;
 const total=Math.ceil(filtered.length/PAGE_SIZE);
 $('#pagination').innerHTML=total>1?`<button data-page="${state.page-1}" ${state.page===1?'disabled':''}>← 上一页</button><span>第 ${state.page} / ${total} 页</span><button data-page="${state.page+1}" ${state.page===total?'disabled':''}>下一页 →</button>`:'';
 $('#export-button').disabled=!filtered.length;
 syncControls();updateUrl();
}
function syncControls(){
 $('#year-filter').value=state.year;$('#search').value=state.search;$('#venue-filter').value=state.venue;$('#sort-select').value=state.sort;$('#published-only').checked=state.published;$('#status-filter').value=state.status;$('#summary-only').checked=state.summary;
}
function resetFilters(){Object.assign(state,{category:'',year:'',venue:'',search:'',status:'',published:false,summary:false,page:1});renderPapers();}
function updateUrl(){
 try{const url=new URL(location.href);url.search='';for(const key of ['category','year','venue','search','status'])if(state[key])url.searchParams.set(key,state[key]);if(state.view!=='papers')url.searchParams.set('view',state.view);if(state.published)url.searchParams.set('published','1');if(state.summary)url.searchParams.set('summary','1');history.replaceState(null,'',url);}catch{}
}
function setView(view){
 state.view=['papers','saved','preprints','sources','about'].includes(view)?view:'papers';state.page=1;
 document.querySelectorAll('.tab').forEach(t=>{t.classList.toggle('active',t.dataset.view===state.view);t.setAttribute('aria-current',t.dataset.view===state.view?'page':'false');});
 $('#papers-view').hidden=!['papers','saved','preprints'].includes(state.view);$('#sources-view').hidden=state.view!=='sources';$('#about-view').hidden=state.view!=='about';
 if(state.view==='sources')renderSources();else if(state.view==='about')renderAbout();else renderPapers();updateUrl();
}
function renderSources(){
 const venues={};for(const p of papers)venues[p.venue]=(venues[p.venue]||0)+1;
 const sourceNames={'arxiv-rss':'arXiv 官方 RSS · 近期论文',arxiv:'arXiv API · 历史与近期',datacite:'DataCite · arXiv DOI 注册元数据',crossref:'Crossref 出版社元数据',cvf:'CVF Open Access',pmlr:'PMLR · ICML',neurips:'NeurIPS 官方论文集',iclr:'ICLR 官方论文集'};
 const statusNames={ok:'本轮扫描完成',incomplete:'分页补录中',error:'本轮访问失败',running:'采集中'};
 $('#sources-view').innerHTML=`${isUpdateDelayed()?'<div class="notice" role="status">更新延迟：已超过 26 小时未生成新索引，当前保留上一版资料。可继续阅读，最近更新时间见下方。</div>':' '}<h2 class="content-heading">每一条记录，都有来源。</h2><p class="content-lead">这里展示实际的数据覆盖和更新状态。关注列表是检索目标，已收录数量代表当前结果；两者不等同于完整覆盖。</p><div class="notice">${esc(meta.coverage_note||'首批论文已核验，历史资料继续补录。数据库未声称穷尽全部相关论文；检索词、来源可用性及出版社元数据延迟都会影响召回。')}</div><div class="info-block"><h3>更新记录</h3><dl class="dialog-details"><div><dt>索引生成</dt><dd>${esc(meta.generated_at||'尚未生成')}</dd></div><div><dt>采集目标</dt><dd>${esc(meta.coverage_start||'2025-01-01')} 至 ${esc(meta.coverage_end||'待定')}</dd></div><div><dt>最近全源成功</dt><dd>${esc(meta.last_successful_update||'尚无全源成功记录')}</dd></div><div><dt>每日任务</dt><dd>${meta.schedule?.configured?`已配置 · 每天 ${esc(scheduleText())} · Asia/Shanghai`:'尚未启用云端定时任务'}</dd></div><div><dt>待审预印本</dt><dd>${Number(meta.candidate_count||0)} 篇</dd></div><div><dt>中文导读</dt><dd>${papers.filter(hasSummary).length} / ${papers.length} 篇已完成</dd></div></dl></div><div class="coverage-grid">${sources.length?sources.map(s=>`<div class="coverage-card"><h4>${esc(sourceNames[s.name]||s.name)}</h4><p>最近尝试：${esc(dateText(s.last_attempt))}</p><p>最近完成扫描：${esc(dateText(s.last_success))}</p><p>最近尝试命中：${Number(s.records_found||0)} 条</p><span class="badge ${s.status==='ok'?'published':'neutral'}">${esc(statusNames[s.status]||s.status)}</span>${s.status==='error'?'<p>源站暂时无法访问，已有论文继续保留。</p>':''}</div>`).join(''):'<div class="coverage-card"><h4>已核验的初始资料</h4><p>依据官方论文页面和出版社元数据整理。自动采集的执行记录将在任务运行后显示。</p><span class="badge neutral">首批导入</span></div>'}</div><div class="info-block" style="margin-top:20px"><h3>已收录的会议与期刊</h3><div class="venue-tags">${Object.keys(venues).sort().map(v=>`<button class="venue-tag" data-venue="${esc(v)}">${esc(v)} · ${venues[v]}</button>`).join('')}</div><p>完整性需要逐届官方目录交叉核验。ICML、ICLR、NeurIPS 等方向的覆盖以此处实际数量为准。</p></div><div class="info-block"><h3>可复用的开放索引</h3><p>引用信息来自论文作者和出版方。中文导读为辅助阅读的概述，具体结论请以原论文为准。导出内容只包括元数据与简介，不托管受限制的论文全文。</p><div class="data-downloads"><a class="button" href="data/papers.json" download="spatial-atlas-papers.json">↓ 下载完整 JSON</a><button class="button" data-export-all>↓ 下载全部 BibTeX</button></div></div>`;
}
function renderAbout(){
 $('#about-view').innerHTML=`<h2 class="content-heading">为长期研究，建立一个起点。</h2><p class="content-lead">Spatial Atlas 收集自 2025 年起正式发表或首次公开的相关研究，以定位、几何与自主导航为主线，帮助研究者找到论文并回到原始证据。</p><div class="info-block"><h3>01 / 研究范围</h3><p>覆盖视觉定位与重定位、点云定位、视觉及点云位置识别、点云配准、点云分割/补全/去噪/采样，以及无人机定位导航。论文可同时属于多个方向，分类数量相加可能大于论文总数。</p></div><div class="info-block"><h3>02 / 发表信息如何确认</h3><p>优先使用官方论文集、出版社页面和 DOI 元数据。预印本与正式发表版本尽可能合并，保留其出处信息；已录用但尚无正式出版记录的论文也纳入论文库，标为「已录用 / 待出版」，并区分官方确认与作者声明。仅有作者声明时，保留其原文与链接，出版状态仍需核验。后续找到正式论文集或出版社记录后，合并更新为「正式发表」。主会与 Workshop 分别核验，Workshop 声明不会自动认作主会录用。</p><p>已录用论文同时保留预印本公开年份和录用会议届次，年份筛选可匹配两者；其他论文按正式出版信息或预印本公开时间记录。只有年份/月的来源，不补造具体日。2025 年前公开但在 2025 年及之后正式发表的论文也在范围内。</p></div><div class="info-block"><h3>03 / 会议期刊与预印本</h3><p>重点关注 TPAMI、IJCV、CVPR、ICCV、ECCV、NeurIPS、AAAI、ICML、ICLR、TIP，以及 TRO、IJRR、ICRA、IROS、RA-L、RSS 等。关注列表不把所有机器人会议期刊统一标成 CCF A。实际收录情况见「来源与更新」。</p><p>arXiv 中主题相关且具有明确录用信息的论文可提前收录；没有录用信息的候选仍需额外筛选，结合方法相关性、公开实验、代码与后续发表证据记录入选理由。进入论文库不意味着已通过同行评审，也不构成质量保证。</p></div><div class="info-block"><h3>04 / 中文导读与更新</h3><p>中文导读以原文摘要为依据，通常约 100–200 字，概述问题、动机和核心方法。自动生成内容标注 AI；摘要信息不足或生成失败时明确显示待补充，不以套话替代具体方法。</p><p>每日任务会检查新论文及已有 arXiv 元数据中的录用声明更新，同时续传历史回溯；去重后更新本地索引，采集异常时保留上一版。源站更新延迟和关键词检索都有局限，无法承诺绝对无遗漏。页面展示实际更新时间与覆盖状态。</p></div><div class="info-block"><h3>05 / 阅读与使用</h3><ul><li>输入标题、作者、方法名或中文关键词，可与方向和出处筛选组合使用。</li><li>按「/」聚焦搜索，点击标题查看完整作者、原文摘要与核验信息。</li><li>星标收藏只保存在当前浏览器；BibTeX 可导出当前筛选结果。</li><li>网站界面、索引与导读由本站提供；原文和代码链接打开各自的外部网站。</li></ul></div>`;
}
function showPaper(id){
 const p=allPapers().find(p=>p.id===id);if(!p)return;
 $('#dialog-content').innerHTML=`<span class="venue-badge">${esc(venueLabel(p))}</span> ${publicationBadge(p)}<h2 class="dialog-title">${esc(p.title)}</h2><p class="paper-authors">${esc(paperAuthors(p).join(', '))}</p><div class="topic-tags">${p.categories.map(c=>`<span class="topic-tag">${esc(CATEGORY_NAMES[c]||c)}</span>`).join('')}</div><div class="dialog-summary"><span class="summary-label">中文导读${p.summary_status==='generated'?' · AI 生成':''}</span>${esc(p.summary_zh||'中文导读尚待补充，请参考下方原文与摘要。')}</div>${acceptanceDetails(p)}<dl class="dialog-details"><div><dt>${p.publication_status==='accepted'?'录用出处':'发表出处'}</dt><dd>${esc(venueLabel(p))}</dd></div><div><dt>${p.publication_status==='accepted'?acceptedDateLabel(p):'日期'}</dt><dd>${esc(p.published||p.year)} ${p.earliest_known_date||p.first_public_date?' · 最早已知记录 '+esc(p.earliest_known_date||p.first_public_date):''}</dd></div>${p.venue_track?`<div><dt>会议轨道</dt><dd>${esc(p.venue_track)}</dd></div>`:''}${p.volume||p.issue||p.pages?`<div><dt>卷期页码</dt><dd>${esc([p.volume?'第 '+p.volume+' 卷':'',p.issue?'第 '+p.issue+' 期':'',p.pages?'页 '+p.pages:''].filter(Boolean).join(' · '))}</dd></div>`:''}${p.publication_date_note?`<div><dt>日期说明</dt><dd>${esc(p.publication_date_note)}</dd></div>`:''}${p.venue_claim?`<div><dt>作者声明</dt><dd>${esc(p.venue_claim)}（尚需出版方核验）</dd></div>`:''}${p.doi?`<div><dt>DOI</dt><dd>${link('https://doi.org/'+p.doi,esc(p.doi))}</dd></div>`:''}${p.arxiv_id?`<div><dt>arXiv</dt><dd>${link('https://arxiv.org/abs/'+p.arxiv_id,esc(p.arxiv_id))}</dd></div>`:''}<div><dt>核验来源</dt><dd>${link(p.evidence_url||p.source_url,esc(p.evidence_url||p.source_url))}</dd></div><div><dt>核验日期</dt><dd>${esc(p.verified_at||'自动采集，见来源')}</dd></div>${p.metadata_note?`<div><dt>元数据说明</dt><dd>${esc(p.metadata_note)}</dd></div>`:''}${p.quality_note?`<div><dt>收录备注</dt><dd>${esc(p.quality_note)}</dd></div>`:''}</dl>${p.abstract?`<details class="dialog-abstract"><summary>查看原文摘要</summary><p>${esc(p.abstract)}</p></details>`:''}<div class="dialog-links">${link(p.source_url,'打开原文 ↗','button primary')}${link(p.pdf_url,'阅读 PDF ↗','button')}${link(p.code_url,'代码仓库 ↗','button')}<button class="button" data-cite="${esc(p.id)}">复制 BibTeX</button></div>`;
 $('#paper-dialog').showModal();
}
function bibtex(p){
 const clean=v=>String(v??'').replace(/\\/g,'\\textbackslash{}').replace(/[{}]/g,'').replace(/[\r\n]+/g,' ').trim();
 const surname=paperAuthors(p)[0]?.split(' ').pop()||'paper';const key=(surname+p.year+p.title.split(/\W+/).slice(0,2).join('')).replace(/[^a-zA-Z0-9]/g,'');
 const journal=/TPAMI|IJCV|TIP|TRO|IJRR|RA-L|Transactions|Journal|Letters/.test(p.venue);const type=p.publication_status!=='published'?'misc':journal?'article':'inproceedings';
 const fields=[['title','{'+clean(p.title)+'}'],['author',paperAuthors(p).map(clean).join(' and ')],['year',p.year],...(p.publication_status!=='published'?[]:[[journal?'journal':'booktitle',p.venue]]),...(journal&&p.publication_status==='published'?['volume','issue','pages'].filter(k=>p[k]).map(k=>[k==='issue'?'number':k,p[k]]):[]),...(p.publication_status==='accepted'?[['note',clean(`Accepted at ${p.accepted_venue||p.venue}${p.accepted_year?' '+p.accepted_year:''}; ${p.acceptance_basis==='official'?(String(p.venue_track||'').includes('待核验')?'official programme listing, track verification pending':'official acceptance'):'author-reported acceptance'}; publication metadata pending`)]]:[]),...(p.doi?[['doi',p.doi]]:[]),...(p.arxiv_id?[['eprint',p.arxiv_id],['archivePrefix','arXiv']]:[]),['url',safeUrl(p.source_url)]];
 return `@${type}{${key},\n`+fields.map(([k,v])=>`  ${k} = {${v}},`).join('\n')+'\n}';
}
function download(text,name,type='text/plain;charset=utf-8'){const url=URL.createObjectURL(new Blob([text],{type}));const a=document.createElement('a');a.href=url;a.download=name;document.body.append(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),5000);}
async function copyCitation(id){const p=allPapers().find(p=>p.id===id);if(!p)return;try{await navigator.clipboard.writeText(bibtex(p));notify('BibTeX 已复制');}catch{download(bibtex(p),p.id+'.bib');notify('已下载 BibTeX 引用');}}
document.addEventListener('click',event=>{
 const target=event.target.closest('button,a');if(!target)return;
 if(target.dataset.view){event.preventDefault();setView(target.dataset.view);}
 if(target.hasAttribute('data-category')){state.category=target.dataset.category;state.page=1;if(!['papers','saved','preprints'].includes(state.view))setView('papers');else renderPapers();}
 if(target.hasAttribute('data-year')){state.year=target.dataset.year;state.page=1;renderPapers();}
 if(target.hasAttribute('data-venue')){state.venue=target.dataset.venue;state.page=1;if(![...$('#venue-filter').options].some(o=>o.value===state.venue))$('#venue-filter').add(new Option(state.venue,state.venue));setView('papers');}
 if(target.dataset.save){const id=target.dataset.save;saved.has(id)?saved.delete(id):saved.add(id);const ok=persist('spatial-atlas:saved',[...saved]);renderPapers();if(!ok)notify('本次收藏仅在当前页面保留，浏览器未允许本地存储');}
 if(target.dataset.paper)showPaper(target.dataset.paper);
 if(target.dataset.cite)copyCitation(target.dataset.cite);
 if(target.dataset.page&&!target.disabled){state.page=Number(target.dataset.page);renderPapers();$('#search').scrollIntoView({behavior:'smooth',block:'start'});}
 if(target.dataset.clear){state[target.dataset.clear]=['published','summary'].includes(target.dataset.clear)?false:'';if(target.dataset.clear==='status')state.published=false;state.page=1;renderPapers();}
 if(target.hasAttribute('data-reset'))resetFilters();
 if(target.hasAttribute('data-export-all')){download(papers.map(bibtex).join('\n\n'),'spatial-atlas-all.bib');notify(`已导出 ${papers.length} 篇论文引用`);}
});
let searchTimer;
$('#search').addEventListener('input',event=>{state.search=event.target.value;state.page=1;clearTimeout(searchTimer);searchTimer=setTimeout(renderPapers,120);});
$('#year-filter').addEventListener('change',e=>{state.year=e.target.value;state.page=1;renderPapers();});
$('#venue-filter').addEventListener('change',e=>{state.venue=e.target.value;state.page=1;renderPapers();});
$('#sort-select').addEventListener('change',e=>{state.sort=e.target.value;state.page=1;renderPapers();});
$('#published-only').addEventListener('change',e=>{state.published=e.target.checked;state.status=state.published?'published':'';state.page=1;renderPapers();});
$('#status-filter').addEventListener('change',e=>{state.status=e.target.value;state.published=state.status==='published';state.page=1;renderPapers();});
$('#summary-only').addEventListener('change',e=>{state.summary=e.target.checked;state.page=1;renderPapers();});
$('#clear-filters').addEventListener('click',resetFilters);
$('#export-button').addEventListener('click',()=>{download(filtered.map(bibtex).join('\n\n'),'spatial-atlas-selection.bib');notify(`已导出 ${filtered.length} 篇论文引用`);});
$('#theme-toggle').addEventListener('click',()=>{const theme=document.documentElement.dataset.theme==='dark'?'light':'dark';document.documentElement.dataset.theme=theme;persist('spatial-atlas:theme',theme);});
$('#dialog-close').addEventListener('click',()=>$('#paper-dialog').close());
$('#paper-dialog').addEventListener('click',event=>{if(event.target===$('#paper-dialog')){const r=event.target.getBoundingClientRect();if(event.clientX<r.left||event.clientX>r.right||event.clientY<r.top||event.clientY>r.bottom)event.target.close();}});
document.addEventListener('keydown',event=>{if(event.key==='/'&&!['INPUT','TEXTAREA','SELECT'].includes(document.activeElement.tagName)&&!$('#paper-dialog').open){event.preventDefault();if(!['papers','saved','preprints'].includes(state.view))setView('papers');$('#search').focus();}});
async function init(){
 try{
  const response=await fetch('data/papers.json',{cache:'no-cache'});if(!response.ok)throw new Error('HTTP '+response.status);const payload=await response.json();
  if(!Array.isArray(payload.papers))throw new Error('Invalid data');
  papers=payload.papers.map(p=>({...p,authors:paperAuthors(p),categories:Array.isArray(p.categories)?p.categories:[]}));preprints=(payload.preprints||[]).map(p=>({...p,authors:paperAuthors(p),categories:Array.isArray(p.categories)?p.categories:[]}));meta=payload.meta||{};sources=payload.sources||[];
  const params=new URL(location.href).searchParams;for(const key of ['category','year','venue','search','status'])state[key]=params.get(key)||'';state.status=['published','accepted','preprint'].includes(state.status)?state.status:'';if(!state.status&&params.get('published')==='1')state.status='published';state.published=state.status==='published';state.summary=params.get('summary')==='1';if(!CATEGORIES.some(c=>c.id===state.category))state.category='';
  populateVenues();updateCounts();renderStatus();setView(params.get('view')||'papers');
 }catch(error){$('#results-label').textContent='索引加载失败';$('#update-status').textContent='无法读取论文索引';$('#paper-list').innerHTML='<div class="empty-state"><span class="empty-icon">⌕</span><h3>暂时无法加载论文库</h3><p>请检查网络后重试。如果在本地浏览，请通过提供的预览命令启动网站。</p><button class="button" id="retry-load">重新加载</button></div>';$('#retry-load').addEventListener('click',init);console.error('Catalogue load failed:',error.message);}
}
init();
