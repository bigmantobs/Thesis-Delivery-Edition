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

pred terminateCheck(ps: ProcessSnapshot) {
	#ps.tokens = 0
}

pred terminates[] {
	(some ps: ProcessSnapshot | terminateCheck[ps])
}

pred unsafe[] {
	(some t,t1 : Token | unsafeHelper[t,t1])
}

pred unsafeHelper(t,t1 : Token) {
	t != t1
	t.pos = t1.pos
}


pred init [] {
	#Process = 0
	#StartEvent = 1
	#Activity = 2
	#PaGate = 2
	#ExGate = 0
	#Token = 1 
	#EndEvent = 1
	#SequenceFlow = 6
	#ProcessSnapshot = 1
	some pSnapshot:ProcessSnapshot, s0:StartEvent, a0,a1:Activity, p0,p1:PaGate, e0:EndEvent {
		#s0.incomingSequenceFlows = 0
		#s0.outgoingSequenceFlows = 1
		s0.outgoingSequenceFlows.target = p0
		p0.incomingSequenceFlows.source = s0
		#p0.incomingSequenceFlows = 1
		#p0.outgoingSequenceFlows = 2
		p0.outgoingSequenceFlows.target = a0+a1
		a0.incomingSequenceFlows.source = s0
		#a0.incomingSequenceFlows = 1
		#a0.outgoingSequenceFlows = 1
		a0.outgoingSequenceFlows.target = a1
		a1.incomingSequenceFlows.source = p0
		#a1.incomingSequenceFlows = 1
		#a1.outgoingSequenceFlows = 1
		a1.outgoingSequenceFlows.target = p1
		p1.incomingSequenceFlows.source = a1+a0
		#p1.incomingSequenceFlows = 2
		#p1.outgoingSequenceFlows = 1
		p1.outgoingSequenceFlows.target = e0
		e0.incomingSequenceFlows.source = p1
		#e0.incomingSequenceFlows = 1
		#e0.outgoingSequenceFlows = 0
        one t: pSnapshot.tokens {
            t.pos = s0
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
	init and always trans and eventually terminates and not eventually unsafe
}

run System for 13 steps, 3 Token, 6 FlowNode, 6 SequenceFlow, 0 Process, 2 Activity, 1 StartEvent, 1 EndEvent, 1 ProcessSnapshot, 0 ExGate, 2 PaGate