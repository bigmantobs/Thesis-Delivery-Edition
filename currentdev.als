// Process
sig Process {
	name: lone String,
	flowNodes: set FlowNode
}

// Flow node
abstract sig FlowNode {
	// sequence flows
	outgoingSequenceFlows: set SequenceFlow,
	incomingSequenceFlows: set SequenceFlow,
}

// Special flow nodes.
sig Activity extends FlowNode {
}

sig StartEvent extends FlowNode {
}

sig EndEvent extends FlowNode {
}

sig ExGate extends FlowNode {
}

sig PaGate extends FlowNode {
}

// Sequence flow
sig SequenceFlow {
	// Not needed atm.
	source: one FlowNode,
	target: one FlowNode
}

fact {
	// Make sequence flow source (target) symmetric to outgoingSequenceFlows (incomingSequenceFlows)
	all s:StartEvent {
		outSFs[s]
	}
	all a:Activity {
		incSFs[a]
		outSFs[a]
	}
	all e:EndEvent {
		incSFs[e]
	}
}

pred incSFs(f:FlowNode) {
		f.incomingSequenceFlows.target = f
}

pred outSFs(f:FlowNode) {
		f.outgoingSequenceFlows.source = f
}

//Token sig + handling
var sig Token {
	var pos: one StartEvent + Activity + SequenceFlow
}

sig ProcessSnapshot {
	var tokens: set Token
}



pred startEventHappens(ps: ProcessSnapshot, s:StartEvent, t:Token) {
	-- pre conditions
	t in ps.tokens
	t.pos = s
	-- post condition
	some newToken : Token'-Token {
		Token' = Token + newToken - t
		//newToken.pos' = s.outgoingSequenceFlows
		pos' = pos + newToken->s.outgoingSequenceFlows - t->s
		tokens' = tokens  + ps->newToken - ps->t
	}
	-- frame conditions
}

pred activityStart(ps: ProcessSnapshot, a:Activity, sf:SequenceFlow) {
	-- pre conditions
	one t: ps.tokens {
		t.pos = sf and sf.target = a
		-- post conditions
		some newToken : Token'-Token {
			Token' = Token + newToken - t
			pos' = pos + newToken->a - t->sf
			tokens' = tokens  + ps->newToken - ps->t
		}
	}
	-- frame conditions
}

pred activityEnd(ps: ProcessSnapshot, a:Activity, sf:SequenceFlow) {
	
	one t: ps.tokens {
		t.pos = a
		some newToken : Token'-Token {
			Token' = Token + newToken - t
			pos' = pos + newToken->a.outgoingSequenceFlows - t->a
			tokens' = tokens  + ps->newToken - ps->t
		}
	}
}

pred exGateHappens (ps: ProcessSnapshot, x:ExGate, isf:SequenceFlow, osf:SequenceFlow) {
	-- pre conditions
	one t: ps.tokens {
		t.pos = isf and isf.target = x
		osf in x.outgoingSequenceFlows
		-- post conditions
		some newToken : Token'-Token {
			Token' = Token + newToken - t
			pos' = pos + newToken->osf - t->isf
			tokens' = tokens  + ps->newToken - ps->t
		}
	}
}

pred paGateHappens (ps: ProcessSnapshot, p:PaGate) {
	-- pre conditions
	let oldTokens = {t: Token | t.pos in p.incomingSequenceFlows} {
		#oldTokens.pos = #p.incomingSequenceFlows

		--post conditions
		let newTokens = Token' - Token {
			Token' = Token + newTokens - oldTokens
			(Token - oldTokens).pos' = (Token - oldTokens).pos
			tokens' = tokens  + ps->newTokens - ps->oldTokens
			newTokens.pos' = p.outgoingSequenceFlows
			#newTokens = #p.outgoingSequenceFlows
		}
	}
}

pred endEventHappens(ps: ProcessSnapshot, e:EndEvent, sf:SequenceFlow) {
	-- pre conditions	
	one t: ps.tokens {
		sf in t.pos and sf.target = e
		-- post conditions
		Token' = Token - t
		pos' = pos - t->sf
		tokens' = tokens - ps->t
	}
	-- frame conditions
}

pred init [] {
	#Process = 0
	#StartEvent = 1
	#EndEvent = 1
	#Activity = 2
	#PaGate = 2
	#Token = 1
	#SequenceFlow = 6
	
	#ProcessSnapshot = 1
	some pSnapshot:ProcessSnapshot, s:StartEvent, g,y: PaGate, b,c:Activity, e:EndEvent {
		// Build the BPMN model
		b!=c
		#s.incomingSequenceFlows = 0
		#s.outgoingSequenceFlows = 1
		s.outgoingSequenceFlows.target = g
		g.incomingSequenceFlows.source = s
		#g.incomingSequenceFlows = 1
		#g.outgoingSequenceFlows = 2
		g.outgoingSequenceFlows.target = b+c
		b.incomingSequenceFlows.source = g
		#b.incomingSequenceFlows = 1
		#b.outgoingSequenceFlows = 1
		b.outgoingSequenceFlows.target = y
		c.incomingSequenceFlows.source = g
		#c.incomingSequenceFlows = 1
		#c.outgoingSequenceFlows = 1
		c.outgoingSequenceFlows.target = y
		y.incomingSequenceFlows.source = b+c
		#y.incomingSequenceFlows = 2
		#y.outgoingSequenceFlows = 1
		y.outgoingSequenceFlows.target = e
		e.incomingSequenceFlows.source = y
		#e.incomingSequenceFlows = 1
		#e.outgoingSequenceFlows = 0

		// Set the start tokens
		one t: pSnapshot.tokens {
			t.pos = s
		}
	}
}


pred trans [] {
	(some ps: ProcessSnapshot, s: StartEvent, t:Token | startEventHappens[ps, s, t])
	or
	(some ps: ProcessSnapshot, a: Activity, sf:SequenceFlow | activityStart[ps, a, sf])
	or
	(some ps: ProcessSnapshot, a: Activity, sf:SequenceFlow | activityEnd[ps, a, sf])
	or
	(some ps: ProcessSnapshot, x: ExGate, isf,osf:SequenceFlow | exGateHappens[ps, x, isf, osf])
	or
	(some ps: ProcessSnapshot, p: PaGate | paGateHappens[ps, p])
	or
	(some ps: ProcessSnapshot, e: EndEvent, sf:SequenceFlow | endEventHappens[ps, e, sf])
	or
	doNothing
	// TODO: Expand with gateways
}

pred doNothing [] {
	-- the relevant relations stay the same
	tokens'=tokens
	Token'=Token
	pos'=pos
}

pred System {
	init and always trans
}

run System for 5 Token, 6 FlowNode, 6 SequenceFlow, 0 Process, 2 Activity, 1 StartEvent, 1 EndEvent, 1 ProcessSnapshot, 0 ExGate, 2 PaGate
