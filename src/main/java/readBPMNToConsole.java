import behavior.bpmn.*;
import org.apache.commons.text.StringSubstitutor;

import java.util.*;
import java.util.stream.Stream;
import java.io.FileWriter;   // Import the FileWriter class
import java.io.IOException;  // Import the IOException class to handle errors

public class readBPMNToConsole implements BPMNToConsoleHelper {
    public static final String BPMN_BPMN_MODELS_READER_TEST = "/testbpms/";

    public String scope = "";
    public static final String TEMPLATE = """
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

${pred}


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

run System for ${scope}""";
// run System for ${scope}
    public int countChar(String str, char c)
    {
        int count = 0;

        for(int i=0; i < str.length(); i++)
        {    if(str.charAt(i) == c)
            count++;
        }

        return count;
    }
    public String getScope() {
        return(this.scope);
    }
    public void setScope(String newscope) {
        this.scope = newscope;
    }
    public String initialization_string_getter(String fileName){
        String init = "";
        {
            BPMNCollaboration result = readModelFromResource(BPMN_BPMN_MODELS_READER_TEST + fileName);
            Set<BPMNProcess> participants = result.getParticipants();
            int processnr = 0;
            Iterator<BPMNProcess> itr = participants.iterator();
            System.out.println("This business process model has " + participants.size() + " processes.");
            while (itr.hasNext()) {
                processnr += 1;
                int gateways = 0;
                int tasks = 0;
                BPMNProcess proc = itr.next();
                Stream<FlowNode> nodes = proc.getFlowNodes();
                Iterator<FlowNode> flowitr = nodes.iterator();
                //if (proc.getSubProcesses().count() > 1) {
                //    Iterator<BPMNEventSubprocess> spitr = proc.getEventSubprocesses().iterator();
                //    BPMNEventSubprocess subproc = spitr.next();
                //    subproc.getName()
                //}
                String flownodeletters = "";
                ArrayList<String> flownodes = new ArrayList<String>();
                int paragates = 0;
                int exgates = 0;
                while (flowitr.hasNext()) {
                    FlowNode node = flowitr.next();
                    String name = node.getName();
                    String nodeClass = node.getClass().toString();
                    if (nodeClass.contains("End")) {
                        name = "e" + Integer.toString((countChar(flownodeletters, 'e')));
                    }
                    if (nodeClass.contains("Task")) {
                        name = "a" + Integer.toString((countChar(flownodeletters, 'a')));
                    }
                    if (nodeClass.contains("Parallel")) {
                        name = "p" + Integer.toString((countChar(flownodeletters, 'p')));
                        paragates +=1;
                    }
                    if (nodeClass.contains("Exclusive")) {
                        name = "x" + Integer.toString((countChar(flownodeletters, 'x')));
                        exgates +=1;
                    }
                    if (nodeClass.contains("Start")) {
                        name = "s" + Integer.toString((countChar(flownodeletters, 's')));
                        flownodeletters = flownodeletters + name;
                    }
                    else {
                        flownodeletters = flownodeletters + " + " + name;
                    }
                    if (node.isGateway()) {
                        gateways += 1;
                    }
                    if (node.isTask()) {
                        tasks += 1;
                    }
                    flownodes.add(name);
                }
                long endevents = proc.getFlowNodes().count() - gateways - tasks - proc.getStartEvents().size();
                System.out.println("The name of the " + processnr + "st the business process model is: " + proc.getName());
                System.out.println("Process " + proc.getName() + " consists of the following:");
                System.out.println(proc.getSequenceFlows().count() + " Sequence Flows");
                System.out.println(proc.getFlowNodes().count() + " Flow Nodes");
                System.out.println("Of these flow nodes, there are " + gateways + " gateway(s), " + proc.getStartEvents().size() + " start event(s)" + ", " + endevents + " end event(s), and " + tasks + " task(s).");
                //Todo: Implement automation in this section.
                /**Suggestion: Generate the p.flownodes and then go through, setting incomingSflows and outgoingSflows according to what
                 * type of flownode it is, f.ex paragate will always have one out and two in, second paragate will always have two in and one out.
                 * startevent has 0 incoming and 1 outgoing
                 * set target of outgoing sequence flows to the next flownode in p.flownodes
                 * String pflow = "s + " + (
                 * activity a1, a2
                 * String substitution org.apache.commons:commons-text
                 **/
                Boolean gatewaytrue = false;
                String scope = (2*proc.getSequenceFlows().count()+1) + " steps, " + (2+paragates/2) + " Token, " + proc.getFlowNodes().count() + " FlowNode, " + proc.getSequenceFlows().count() + " SequenceFlow, " +
                        "0 Process, " + tasks + " Activity, " + proc.getStartEvents().size() + " StartEvent, " +
                        endevents + " EndEvent, " + "1 ProcessSnapshot, " + exgates + " ExGate, " +
                        paragates + " PaGate";
                setScope(scope);
                init = ("\npred init [] {\n" + "\t#Process = 0\n"
                        + "\t#StartEvent = " + proc.getStartEvents().size() + "\n"
                        + "\t#Activity = " + tasks + "\n"
                        + "\t#PaGate = " + paragates + "\n"
                        + "\t#ExGate = " + exgates + "\n"
                        + "\t#Token = 1 \n"
                        + "\t#EndEvent = " + endevents + "\n"
                        + "\t#SequenceFlow = " + proc.getSequenceFlows().count() + "\n"
                        + "\t#ProcessSnapshot = 1" + "\n"
                        + initHelper(flownodes));// iterate through letters in p.flownodes and print #letter.incomingsequenceflows and #letter.outgoingsequenceflows, then target = next letter in p.flownodes
                for (int i = 0; i < flownodes.size();i++) {
                    String currChart = flownodes.get(i);
                    if (currChart.contains("s")) {
                        init = init + "\t\t#"+currChart+".incomingSequenceFlows = 0\n";
                        init = init + "\t\t#"+currChart+".outgoingSequenceFlows = 1\n";
                        init = init + "\t\t"+currChart+".outgoingSequenceFlows.target = " + flownodes.get(i+1) + "\n";
                    }
                    if (currChart.contains("a")) {
                        if (gatewaytrue) {
                            init = init + "\t\t" + currChart + ".incomingSequenceFlows.source = " + flownodes.get(i - 2) + "\n";
                            init = init + "\t\t#" + currChart + ".incomingSequenceFlows = 1\n";
                            init = init + "\t\t#" + currChart + ".outgoingSequenceFlows = 1\n";
                            init = init + "\t\t" + currChart + ".outgoingSequenceFlows.target = " + flownodes.get(i + 1) + "\n";
                        } else {
                            init = init + "\t\t" + currChart + ".incomingSequenceFlows.source = " + flownodes.get(i - 1) + "\n";
                            init = init + "\t\t#" + currChart + ".incomingSequenceFlows = 1\n";
                            init = init + "\t\t#" + currChart + ".outgoingSequenceFlows = 1\n";
                            init = init + "\t\t" + currChart + ".outgoingSequenceFlows.target = " + flownodes.get(i + 1) + "\n";

                        }
                    }
                    if (currChart.contains("p")) {
                        if (!gatewaytrue) {
                            init = init + "\t\t"+currChart+".incomingSequenceFlows.source = " + flownodes.get(i-1) + "\n";
                            init = init + "\t\t#"+currChart+".incomingSequenceFlows = 1\n";
                            init = init + "\t\t#"+currChart+".outgoingSequenceFlows = 2\n";
                            init = init + "\t\t"+currChart+".outgoingSequenceFlows.target = " + flownodes.get(i+1) + "+" + flownodes.get(i+2) + "\n";
                            gatewaytrue = true;
                        }
                        else {
                            init = init + "\t\t"+currChart+".incomingSequenceFlows.source = " + flownodes.get(i-1) + "+" + flownodes.get(i-2) + "\n";
                            init = init + "\t\t#"+currChart+".incomingSequenceFlows = 2\n";
                            init = init + "\t\t#"+currChart+".outgoingSequenceFlows = 1\n";
                            init = init + "\t\t"+currChart+".outgoingSequenceFlows.target = " + flownodes.get(i+1) + "\n";
                            gatewaytrue = false;
                        }
                    }
                    if (currChart.contains("x")) {
                        if (!gatewaytrue) {
                            init = init + "\t\t"+currChart+".incomingSequenceFlows.source = " + flownodes.get(i-1) + "\n";
                            init = init + "\t\t#"+currChart+".incomingSequenceFlows = 1\n";
                            init = init + "\t\t#"+currChart+".outgoingSequenceFlows = 2\n";
                            init = init + "\t\t"+currChart+".outgoingSequenceFlows.target = " + flownodes.get(i+1) + "+" + flownodes.get(i+2) + "\n";
                            gatewaytrue = true;
                        }
                        else {
                            init = init + "\t\t"+currChart+".incomingSequenceFlows.source = " + flownodes.get(i-1) + "+" + flownodes.get(i-2) + "\n";
                            init = init + "\t\t#"+currChart+".incomingSequenceFlows = 2\n";
                            init = init + "\t\t#"+currChart+".outgoingSequenceFlows = 1\n";
                            init = init + "\t\t"+currChart+".outgoingSequenceFlows.target = " + flownodes.get(i+1) + "\n";
                            gatewaytrue = false;
                        }
                    }
                    if (currChart.contains("e")) {
                        init = init + "\t\t"+currChart+".incomingSequenceFlows.source = " + flownodes.get(i-1) + "\n";
                        init = init + "\t\t#"+currChart+".incomingSequenceFlows = 1\n";
                        init = init + "\t\t#"+currChart+".outgoingSequenceFlows = 0\n";
                    }
                }
                init = init + """
                            one t: pSnapshot.tokens {
                                t.pos = s0
                            }
                        }
                    }
                    """;
                //myWriter.write(init);
                //myWriter.write(template_2);
                //myWriter.write((" " + scope));
                //myWriter.close();
            }

        }
        //System.out.println(init);
        return(init);
    }

    public String initHelper(ArrayList<String> list) {
        String output = "\tsome pSnapshot:ProcessSnapshot, ";
        String startevents = "";
        String activites = "";
        String pagates = "";
        String exgates = "";
        String endevent = "";
        Boolean pagatesbool = false;
        Boolean exgatesbool = false;
        for (int i = 0; i < list.size();i++)
        {
            String currChar = list.get(i);
            char currCharChar = currChar.charAt(0);
            switch(currCharChar) {
                case 'a':
                    activites = activites + currChar + ",";
                    break;
                case 's':
                    startevents = startevents + currChar + ",";
                    break;
                case 'p':
                    pagates = pagates + currChar + ",";
                    pagatesbool = true;
                    break;
                case 'x':
                    exgates = exgates + currChar + ",";
                    exgatesbool = true;
                    break;
                case 'e':
                    endevent = endevent + currChar;
                    break;
            }
        }
        startevents = dropLastChar(startevents);
        startevents = startevents + ":StartEvent, ";
        activites = dropLastChar(activites);
        activites = activites + ":Activity, ";
        if (pagatesbool) {
            pagates = dropLastChar(pagates);
            pagates = pagates + ":PaGate, ";
        }
        if (exgatesbool) {
            exgates = dropLastChar(exgates);
            exgates = exgates + ":ExGate, ";
        }
        endevent = endevent + ":EndEvent";
        output = output + startevents + activites + pagates + exgates + endevent + " {\n";
        return(output);
    }
    public String generate(String fileName) {
        Map<String, String> substitutionValues = new HashMap<>();
        substitutionValues.put("pred", initialization_string_getter(fileName));
        String scope = getScope();
        substitutionValues.put("scope",scope);
        return new StringSubstitutor(substitutionValues).replace(TEMPLATE);
    }

    public void printToAlloy(String fileName) throws IOException {
        String alloyCode = generate(fileName);
        try {
            FileWriter myWriter = new FileWriter("bpmn_model_substitutor.als");
            myWriter.write(alloyCode);
            myWriter.close();
            System.out.println("Successfully generated String Substituted file");
        }
        catch (IOException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }
    }
    public String dropLastChar(String word) {
        String output = "";
        for (int i=0; i<word.length()-1;i++) {
            output = output + word.charAt(i);
        }
        return(output);
    }
}
//Gateways are marked as follows --> Parallel: gateway_0 exclusive: gateway_1



/**
    public void processInfoPrinter(AbstractBPMNProcess input) {
        int gateways = 0;
        int tasks = 0;
        Stream<FlowNode> nodes = input.getFlowNodes();
        Iterator<FlowNode> flowitr = nodes.iterator();
        while(flowitr.hasNext()){
            FlowNode node = flowitr.next();
            if (node.isGateway()) {
                gateways +=1;
            }
            if (node.isTask()) {
                tasks +=1;
            }
        }
        System.out.println("Process name is: " + input.getName());
        System.out.println("Process " + input.getName() + " consists of the following:");
        System.out.println(input.getSequenceFlows().count() + " Sequence Flows");
        System.out.println(input.getFlowNodes().count() + " Flow Nodes");
        System.out.println("Of these flow nodes, there are " + gateways + " gateway(s), "+ 1 + " start event(s)" + ", "+ endevents + " end event(s), and " + tasks + " task(s).");
    }

}
**/