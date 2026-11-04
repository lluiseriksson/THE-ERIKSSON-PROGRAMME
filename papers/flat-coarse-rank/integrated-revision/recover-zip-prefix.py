"""Recover complete CRC-checked ZIP members; never validates a whole partial ZIP."""
import hashlib,json,pathlib,struct,sys,zlib
data=pathlib.Path(sys.argv[1]).read_bytes();out=pathlib.Path(sys.argv[2]);out.mkdir(exist_ok=True)
offset=0;entries=[]
while data[offset:offset+4]==b'PK\x03\x04':
    if offset+30>len(data):break
    _,version,flags,method,tm,dt,crc,compressed,size,nlen,xlen=struct.unpack_from('<IHHHHHIIIHH',data,offset)
    if flags&8:raise ValueError('Unknown lengths cannot be accepted')
    name=data[offset+30:offset+30+nlen].decode('utf-8');start=offset+30+nlen+xlen
    if start+compressed>len(data):break
    if pathlib.PurePosixPath(name).name!=name:raise ValueError('Unsafe name')
    raw=data[start:start+compressed]
    content=zlib.decompress(raw,-15) if method==8 else raw if method==0 else None
    if content is None or len(content)!=size or zlib.crc32(content)&0xffffffff!=crc:raise ValueError('CRC/length mismatch')
    (out/name).write_bytes(content);entries.append({'name':name,'bytes':size,'sha256':hashlib.sha256(content).hexdigest()});offset=start+compressed
report={'partial_archive_not_complete':True,'whole_archive_hash_not_verified':True,'complete_entries_crc_checked':entries,'consumed_bytes':offset,'input_bytes':len(data)}
(out/'prefix-recovery-report.json').write_text(json.dumps(report,indent=2))
print(json.dumps({'complete_entries':len(entries),'pages':sum(e['name'].startswith('page-') for e in entries),'last':entries[-1]['name']}))
