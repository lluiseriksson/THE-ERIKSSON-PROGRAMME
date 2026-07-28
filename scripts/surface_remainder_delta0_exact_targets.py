"""Pure symbolic target formulas for the nominal K2 carrier heads."""

from __future__ import annotations


def target_y0(c):
    return (4*c**2-1)/(8*c**3)


def target_y1(c):
    return (-8*c**4+15*c**2-4)/(32*c**6)


def target_y2(c):
    return (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9)


def target_y3(c):
    return (
        28*c**8+41*c**6-1464*c**4+1856*c**2-500
    )/(1024*c**12)


def target_y4(c):
    return (
        12940*c**10+16077*c**8+173288*c**6
        -1300912*c**4+1358400*c**2-346112
    )/(262144*c**15)


def target_y5(c):
    return (
        8148*c**12+17095*c**10+10768*c**8+634576*c**6
        -2557408*c**4+2283296*c**2-549376
    )/(131072*c**18)


def target_y6(c):
    return (
        2085412*c**14+6775103*c**12+11636676*c**10
        -52644752*c**8+1046587520*c**6-2880628992*c**4
        +2254849024*c**2-513015808
    )/(33554432*c**21)


def target_y7(c):
    return (
        19936*c**16+119595*c**14+323054*c**12+637408*c**10
        -12653880*c**8+104539328*c**6-219463616*c**4
        +153352416*c**2-33064504
    )/(524288*c**24)


def frozen_targets(c):
    return [
        target_y0(c),
        target_y1(c),
        target_y2(c),
        target_y3(c),
        target_y4(c),
        target_y5(c),
        target_y6(c),
        target_y7(c),
    ]
