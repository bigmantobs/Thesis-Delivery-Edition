
pred init [] {
	#Process = 1
	#StartEvent = 1
	#EndEvent = 1
	#SequenceFlow = 7
	#ProcessSnapshot = 1
	some pSnapshot:ProcessSnapshot, p:Process, s:StartEvent, a:Activity, g:ParaGate, e:EndEvent {
		p.flownodes = s0 + a0 + g0 + a1 + a2 + g1 + e0
		#s0.incomingSequenceFlows = 0
		#s0.outgoingSequenceFlows = 1
		s0.outgoingSequenceFlows.target = a0
		#a0.incomingSequenceFlows = 1
		#a0.outgoingSequenceFlows = 1
		a0.outgoingSequenceFlows.target = g0
		#g0.incomingSequenceFlows = 1
		#g0.outgoingSequenceFlows = 2
		g0.outgoingSequenceFlows.target = a1
		g0.outgoingSequenceFlows.target = a2
		#a1.incomingSequenceFlows = 1
		#a1.outgoingSequenceFlows = 1
		a1.outgoingSequenceFlows.target = a2
		#a2.incomingSequenceFlows = 1
		#a2.outgoingSequenceFlows = 1
		a2.outgoingSequenceFlows.target = g1
		#g1.incomingSequenceFlows = 2
		#g1.outgoingSequenceFlows = 1
		g1.outgoingSequenceFlows.target = e0
		#e0.incomingSequenceFlows = 1
		#e0.outgoingSequenceFlows = 0
		one t: pSnapshot.tokens {
			t.pos = s
		}
		//pSnapshot.tokens = s
	}
}
pred trans [] {
	(some ps: ProcessSnapshot, s: StartEvent | startEventHappens[ps, s])
	or
	(some ps: ProcessSnapshot, a: Activity, sf:SequenceFlow | activityStarts[ps, a, sf])
	or
	(some ps: ProcessSnapshot, a: Activity, isf:SequenceFlow, osf:SequenceFlow | activityEnds[ps, a, isf, osf])
	or
	(some ps: ProcessSnapshot, g: ParaGate | paraGateExec[ps, g])
	or
	(some ps: ProcessSnapshot, x: ExclGate, isf:SequenceFlow, osf:SequenceFlow | exclGateExec[ps, x, isf, osf])
	or
	(some ps: ProcessSnapshot, e: EndEvent, sf:SequenceFlow | endEventHappens[ps, e, sf])
	or
	//(some ps: ProcessSnapshot  |  spawnToken[ps])
	//or
	doNothing
	// TODO: Expand with gateways
}

pred doNothing [] {
	-- the relevant relations stay the same
	tokens' = tokens
}

pred System {
	init and always trans
}
run System for 8