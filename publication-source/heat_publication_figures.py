"""Recreate the heat benchmark figures: python heat_publication_figures.py RC2.zip figures"""
import csv
import hashlib
import io
import math
from pathlib import Path
import sys
import zipfile

import pypdfium2
from reportlab.pdfgen.canvas import Canvas
from reportlab.lib.colors import HexColor

archive, dest = map(Path, sys.argv[1:])
dest.mkdir(parents=True, exist_ok=True)
def digest(data):
    return hashlib.sha256(data).hexdigest()
if digest(archive.read_bytes()) != "d55c547640122ca101adba48b4fccd4d70067c2978a2a4c96983a76e5079a1b0":
    raise ValueError("Unexpected RC2 archive")
with zipfile.ZipFile(archive) as z:
    prefix = "evidence/cosine-one-invocation-6asyt36h/"
    rows = list(csv.DictReader(io.StringIO(z.read(prefix+"final.csv").decode())))
    initial = [float.fromhex(s) for s in z.read(prefix+"initial.hex").decode().splitlines()]
assert len(rows) == len(initial) == 400
x = [float(r["x"]) for r in rows]
final = [float(r["u"]) for r in rows]
assert all(abs(a-(-3+(i+.5)*.015)) < 2e-15 for i,a in enumerate(x))
h, dt = 1080863910568919/2**56, 5170051590165233/2**60
d, q = 5764607523034235/2**59, 4150517416584649/2**64
decay = math.exp(-(d*h*h/q)*(math.pi/(400*h))**2*(223*dt))
ref = [1+.5*decay*math.cos(math.pi*(2*i+1)/800) for i in range(400)]
error = [abs(a-b) for a,b in zip(final,ref)]
change = [1000*(a-b) for a,b in zip(final,initial)]
teal, navy, orange, grey = "#006e70", "#192f45", "#af4818", "#526579"

def label(c,x,y,s,size=11,color=navy,bold=False):
    c.setFillColor(HexColor(color)); c.setFont("Helvetica-Bold" if bold else "Helvetica",size)
    c.drawString(x,y,s)

def axes(c,bottom,top,lo,hi,ticks):
    left,right=80,684
    def xy(a,b):
        return left+(a+3)/6*(right-left),bottom+(b-lo)/(hi-lo)*(top-bottom)
    for v in ticks:
        _,y=xy(0,v)
        c.setStrokeColor(HexColor("#dbe3e8")); c.setLineWidth(.6); c.line(left,y,right,y)
        c.setFont("Helvetica",10); c.setFillColor(HexColor(grey)); c.drawRightString(left-8,y-3,f"{v:g}")
    for v in range(-3,4):
        xx,_=xy(v,0)
        c.setFillColor(HexColor(grey)); c.drawCentredString(xx,bottom-15,str(v))
    return xy

def line(c,xy,points,color,dashed=False):
    p=c.beginPath()
    for i,(a,b) in enumerate(points):
        (p.moveTo if i==0 else p.lineTo)(*xy(a,b))
    c.setStrokeColor(HexColor(color)); c.setLineWidth(2)
    c.setDash([5,4] if dashed else []); c.drawPath(p); c.setDash([])

def finish(c,name):
    c.showPage(); c.save()
    with pypdfium2.PdfDocument(dest/(name+".pdf")) as doc:
        doc[0].render(scale=2.5).to_pil().save(dest/(name+".png"))

name="heat-profile"
c=Canvas(str(dest/(name+".pdf")),pagesize=(730,520),invariant=1)
label(c,34,480,"Diffusion of a cosine profile",25,bold=True)
label(c,34,457,"One instrumented C execution  |  400 cell centers  |  223 Heun steps",12,grey)
label(c,80,416,"Final cell value",13,bold=True)
line(c,axes(c,277,400,.45,1.55,[.5,1,1.5]),zip(x,final),teal)
label(c,80,230,"Change from initialization  (final minus initial, units of 0.001)",13,bold=True)
line(c,axes(c,90,213,-1.5,1.5,[-1.5,0,1.5]),zip(x,change),teal)
label(c,340,54,"Position x"); label(c,34,21,"Initial and final values were captured in the same invocation.",10,grey)
finish(c,name)

name="heat-error"
c=Canvas(str(dest/(name+".pdf")),pagesize=(730,420),invariant=1)
label(c,34,378,"Final error across the grid",25,bold=True)
label(c,34,355,"Absolute difference from the effective-diffusivity cosine reference",12,grey)
label(c,80,316,"Error in units of 10^-9",12,bold=True)
xy=axes(c,100,274,0,8,[0,2,4,6,8])
line(c,xy,[(-3,7.05),(3,7.05)],orange,True)
line(c,xy,zip(x,[v*1e9 for v in error]),teal)
label(c,80,292,"Measured C error",11,teal,True)
label(c,370,292,"Dashed: Lean model bound (7.05)",11,orange,True)
label(c,340,63,"Position x")
label(c,34,34,f"Peak measured difference: {max(error):.4g}. Reference evaluated numerically.",11,grey)
label(c,34,16,"The dashed line applies to the rounded model under its initial-error hypothesis.",10,grey)
finish(c,name)
print("Peak measured absolute difference",max(error),"cell",error.index(max(error)))
