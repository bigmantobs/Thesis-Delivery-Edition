package behavior.bpmn.reader;

import behavior.bpmn.BPMNCollaboration;
import behavior.bpmn.activities.CallActivity;
import behavior.bpmn.activities.tasks.ReceiveTask;
import behavior.bpmn.activities.tasks.SendTask;
import behavior.bpmn.activities.tasks.Task;
import behavior.bpmn.auxiliary.BPMNCollaborationBuilder;
import behavior.bpmn.auxiliary.BPMNEventSubprocessBuilder;
import behavior.bpmn.auxiliary.BPMNModelBuilder;
import behavior.bpmn.auxiliary.BPMNProcessBuilder;
import behavior.bpmn.auxiliary.exceptions.BPMNRuntimeException;
import behavior.bpmn.events.EndEvent;
import behavior.bpmn.events.IntermediateCatchEvent;
import behavior.bpmn.events.IntermediateThrowEvent;
import behavior.bpmn.events.StartEvent;
import behavior.bpmn.events.*;
import behavior.bpmn.gateways.EventBasedGateway;
import behavior.bpmn.gateways.ExclusiveGateway;
import behavior.bpmn.gateways.InclusiveGateway;
import behavior.bpmn.gateways.ParallelGateway;
import org.apache.commons.io.FilenameUtils;
import org.camunda.bpm.model.bpmn.Bpmn;
import org.camunda.bpm.model.bpmn.BpmnModelInstance;
import org.camunda.bpm.model.bpmn.instance.BoundaryEvent;
import org.camunda.bpm.model.bpmn.instance.*;
import org.camunda.bpm.model.bpmn.instance.camunda.CamundaProperties;
import org.camunda.bpm.model.xml.instance.ModelElementInstance;
import org.camunda.bpm.model.xml.type.ModelElementType;

import java.io.File;
import java.io.InputStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.function.UnaryOperator;

public class BPMNFileReader {

  private Function<String, String> elementNameTransformer;

  public BPMNFileReader() {}

  public BPMNFileReader(UnaryOperator<String> elementNameTransformer) {
    this.elementNameTransformer = elementNameTransformer;
  }

  public BPMNCollaboration readModelFromFile(File file) {
    BpmnModelInstance bpmnModelInstance = Bpmn.readModelFromFile(file);
    return convertModel(FilenameUtils.removeExtension(file.getName()), bpmnModelInstance);
  }

  public BPMNCollaboration readModelFromStream(InputStream stream) {
    BpmnModelInstance bpmnModelInstance = Bpmn.readModelFromStream(stream);
    return convertModel("model", bpmnModelInstance);
  }

  private BPMNCollaboration convertModel(
      String collaborationName, BpmnModelInstance bpmnModelInstance) {
    BPMNCollaborationBuilder bpmnCollaborationBuilder =
        new BPMNCollaborationBuilder().name(collaborationName);

    Map<String, behavior.bpmn.FlowNode> mappedFlowNodes = new HashMap<>();
    Map<String, Boolean> mappedSequenceFlows = new HashMap<>();

    // Map subprocesses
    ModelElementType subprocessType = bpmnModelInstance.getModel().getType(SubProcess.class);
    Collection<ModelElementInstance> subprocesses =
        bpmnModelInstance.getModelElementsByType(subprocessType);
    subprocesses.forEach(
        subProcessModelElement -> {
          SubProcess subProcess = (SubProcess) subProcessModelElement;
          behavior.bpmn.FlowNode mappedSubprocessIfExists = mappedFlowNodes.get(subProcess.getId());
          if (mappedSubprocessIfExists == null && !subProcess.triggeredByEvent()) {
            mapSubProcess(subProcess, mappedFlowNodes, mappedSequenceFlows);
          }
        });

    // Map participants/pools
    ModelElementType participantType = bpmnModelInstance.getModel().getType(Participant.class);
    Collection<ModelElementInstance> participants =
        bpmnModelInstance.getModelElementsByType(participantType);
    if (participants.isEmpty()) {
      bpmnCollaborationBuilder.processName(collaborationName);
      mapModelInstanceToOneParticipant(
          bpmnModelInstance, bpmnCollaborationBuilder, mappedFlowNodes, mappedSequenceFlows);
    } else {
      // Map each participant
      participants.forEach(
          modelElementInstance ->
              mapParticipant(
                  bpmnCollaborationBuilder,
                  mappedFlowNodes,
                  mappedSequenceFlows,
                  (Participant) modelElementInstance));
      // Map message flows
      mapMessageFlows(
          bpmnModelInstance, bpmnCollaborationBuilder, mappedFlowNodes, mappedSequenceFlows);
    }
    return bpmnCollaborationBuilder.build();
  }

  private void mapMessageFlows(
      BpmnModelInstance bpmnModelInstance,
      BPMNCollaborationBuilder bpmnCollaborationBuilder,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows) {
    ModelElementType mfType = bpmnModelInstance.getModel().getType(MessageFlow.class);
    Collection<ModelElementInstance> messageFlowModelElements =
        bpmnModelInstance.getModelElementsByType(mfType);
    messageFlowModelElements.forEach(
        modelElementInstance ->
            mapMessageFlow(
                (MessageFlow) modelElementInstance,
                bpmnCollaborationBuilder,
                mappedFlowNodes,
                mappedSequenceFlows));
  }

  private void mapMessageFlow(
      MessageFlow messageFlow,
      BPMNCollaborationBuilder bpmnCollaborationBuilder,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows) {
    InteractionNode sourceInteractionNode = messageFlow.getSource();
    InteractionNode targetInteractionNode = messageFlow.getTarget();
    if (!(sourceInteractionNode instanceof FlowNode)) {
      throw new BPMNRuntimeException(
          String.format(
              "Message flow with id \"%s\" has an invalid source with id "
                  + "\"%s\", which is not a flow node (event, activity, ...)!",
              messageFlow.getId(), sourceInteractionNode.getId()));
    }
    if (!(targetInteractionNode instanceof FlowNode)) {
      throw new BPMNRuntimeException(
          String.format(
              "Message flow with id \"%s\" has an invalid target with id "
                  + "\"%s\", which is not a flow node (event, activity, ...)!",
              messageFlow.getId(), targetInteractionNode.getId()));
    }
    FlowNode source = (FlowNode) sourceInteractionNode;
    FlowNode target = (FlowNode) targetInteractionNode;
    bpmnCollaborationBuilder.messageFlow(
        messageFlow.getId(),
        messageFlow.getName() == null ? "" : messageFlow.getName(),
        mapFlowNode(source, mappedFlowNodes, mappedSequenceFlows, bpmnCollaborationBuilder),
        mapFlowNode(target, mappedFlowNodes, mappedSequenceFlows, bpmnCollaborationBuilder));
  }

  private void mapModelInstanceToOneParticipant(
      BpmnModelInstance bpmnModelInstance,
      BPMNCollaborationBuilder bpmnCollaborationBuilder,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows) {
    // Map subprocesses since they might not be connected by sequence flows (event subprocesses for
    // example).
    ModelElementType spType = bpmnModelInstance.getModel().getType(SubProcess.class);
    Collection<ModelElementInstance> subProcessModelElements =
        bpmnModelInstance.getModelElementsByType(spType);
    subProcessModelElements.forEach(
        flowNodeModelElement -> {
          FlowNode flowNode = (FlowNode) flowNodeModelElement;
          mapFlowNode(flowNode, mappedFlowNodes, mappedSequenceFlows, bpmnCollaborationBuilder);
        });
    ModelElementType sfType = bpmnModelInstance.getModel().getType(FlowElement.class);
    Collection<ModelElementInstance> sequenceFlowModelElements =
        bpmnModelInstance.getModelElementsByType(sfType);
    sequenceFlowModelElements.forEach(
        sequenceFlowModelElement -> {
          FlowElement flowElement = (FlowElement) sequenceFlowModelElement;
          mapFlowElement(
              bpmnCollaborationBuilder, mappedFlowNodes, mappedSequenceFlows, flowElement);
        });
  }

  private void mapParticipant(
      BPMNCollaborationBuilder bpmnCollaborationBuilder,
      Map<String, behavior.bpmn.FlowNode> createdFlowNodes,
      Map<String, Boolean> mappedSequenceFlows,
      Participant participant) {
    bpmnCollaborationBuilder.processName(participant.getName());
    participant
        .getProcess()
        .getFlowElements()
        .forEach(
            flowElement ->
                mapFlowElement(
                    bpmnCollaborationBuilder, createdFlowNodes, mappedSequenceFlows, flowElement));
    bpmnCollaborationBuilder.buildProcess();
  }

  private void mapFlowElement(
      BPMNModelBuilder bpmnModelBuilder,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows,
      FlowElement flowElement) {
    // Map flow nodes
    if (flowElement instanceof FlowNode) {
      mapFlowNode((FlowNode) flowElement, mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder);
    }
    // Map sequence flows
    if (flowElement instanceof SequenceFlow) {
      SequenceFlow sequenceFlow = (SequenceFlow) flowElement;
      mapSequenceFlow(sequenceFlow, mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder);
    }
  }

  private void mapSequenceFlow(
      SequenceFlow sequenceFlow,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows,
      BPMNModelBuilder bpmnModelBuilder) {
    Boolean sequenceFlowMapped = mappedSequenceFlows.get(sequenceFlow.getId());
    if (sequenceFlowMapped != null && sequenceFlowMapped) {
      // Sequence flow has been mapped already.
      return;
    }
    if (sequenceFlow.getName() == null || sequenceFlow.getName().isEmpty()) {
      bpmnModelBuilder.sequenceFlow(
          sequenceFlow.getId(),
          mapFlowNode(
              sequenceFlow.getSource(), mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder),
          mapFlowNode(
              sequenceFlow.getTarget(), mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder));
    } else {
      bpmnModelBuilder.sequenceFlow(
          sequenceFlow.getId(),
          getFlowElementName(sequenceFlow),
          mapFlowNode(
              sequenceFlow.getSource(), mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder),
          mapFlowNode(
              sequenceFlow.getTarget(), mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder));
    }
    mappedSequenceFlows.put(sequenceFlow.getId(), true);
  }

  private behavior.bpmn.FlowNode mapFlowNode(
      FlowNode flowNode,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows,
      BPMNModelBuilder bpmnModelBuilder) {
    behavior.bpmn.FlowNode flowNodeIfExists = mappedFlowNodes.get(flowNode.getId());
    if (flowNodeIfExists != null) {
      return flowNodeIfExists;
    }
    String taskTypeName = flowNode.getElementType().getTypeName();
    behavior.bpmn.FlowNode resultingFlowNode;
    switch (taskTypeName) {
        // Events
      case "startEvent":
        StartEvent startEvent = mapStartEvent(flowNode);
        bpmnModelBuilder.startEvent(startEvent);
        resultingFlowNode = startEvent;
        break;
      case "intermediateThrowEvent":
        resultingFlowNode = this.mapIntermediateThrowEvent(flowNode);
        break;
      case "intermediateCatchEvent":
        resultingFlowNode = this.mapIntermediateCatchEvent(flowNode);
        break;
      case "endEvent":
        resultingFlowNode = mapEndEvent(flowNode);
        break;
        // Tasks
      case "businessRuleTask":
      case "scriptTask":
      case "serviceTask":
      case "manualTask":
      case "userTask":
      case "task":
        resultingFlowNode = new Task(flowNode.getId(), getFlowElementName(flowNode));
        break;
      case "sendTask":
        resultingFlowNode = new SendTask(flowNode.getId(), getFlowElementName(flowNode));
        break;
      case "receiveTask":
        boolean instantiate = hasInstantiateCamundaProperty(flowNode);
        resultingFlowNode =
            new ReceiveTask(flowNode.getId(), getFlowElementName(flowNode), instantiate);
        break;
      case "subProcess":
        SubProcess subprocess = (SubProcess) flowNode;
        if (subprocess.triggeredByEvent()) {
          handleEventSubProcess(subprocess, mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder);
          resultingFlowNode = null;
          // This is ok since no sequence flows can start or end in an event subprocess.
        } else {
          resultingFlowNode = mapSubProcess(subprocess, mappedFlowNodes, mappedSequenceFlows);
        }
        break;
      case "callActivity":
        // Call Activity = Reusable sub-processes (external).
        throw new BPMNRuntimeException("External subprocesses currently not supported!");
        // Gateways
      case "parallelGateway":
        resultingFlowNode = new ParallelGateway(flowNode.getId(), getFlowElementName(flowNode));
        break;
      case "exclusiveGateway":
        resultingFlowNode = new ExclusiveGateway(flowNode.getId(), getFlowElementName(flowNode));
        break;
      case "eventBasedGateway":
        boolean instantiateGateway = hasInstantiateCamundaProperty(flowNode);
        resultingFlowNode =
            new EventBasedGateway(
                flowNode.getId(), getFlowElementName(flowNode), instantiateGateway);
        break;
      case "inclusiveGateway":
        resultingFlowNode = new InclusiveGateway(flowNode.getId(), getFlowElementName(flowNode));
        break;
      case "boundaryEvent":
        resultingFlowNode =
            handleBoundaryEvent(flowNode, mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder);
        break;
      default:
        throw new BPMNRuntimeException(
            String.format("Unknown task type \"%s\" found!", taskTypeName));
    }
    if (resultingFlowNode != null) {
      bpmnModelBuilder.flowNode(resultingFlowNode);
      mappedFlowNodes.put(flowNode.getId(), resultingFlowNode);
    }
    return resultingFlowNode;
  }

  private String getFlowElementName(FlowElement flowElement) {
    if (flowElement.getName() == null) {
      return flowElement.getId();
    }
    if (this.elementNameTransformer != null) {
      return elementNameTransformer.apply(flowElement.getName());
    }
    return flowElement.getName();
  }

  private behavior.bpmn.FlowNode handleBoundaryEvent(
      FlowNode flowNode,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows,
      BPMNModelBuilder bpmnModelBuilder) {
    BoundaryEvent event = (BoundaryEvent) flowNode;
    Collection<EventDefinition> eventDefinitions = event.getEventDefinitions();
    behavior.bpmn.events.BoundaryEvent boundaryEvent;
    if (eventDefinitions.size() != 1) {
      boundaryEvent =
          new behavior.bpmn.events.BoundaryEvent(
              flowNode.getId(),
              getFlowElementName(event),
              BoundaryEventType.NONE,
              event.cancelActivity());
    } else {
      boundaryEvent = getBoundaryEventWithDefinition(event, eventDefinitions.iterator().next());
    }
    // AttachedTo must be an activity
    behavior.bpmn.activities.Activity attachedTo =
        (behavior.bpmn.activities.Activity)
            mapFlowNode(
                event.getAttachedTo(), mappedFlowNodes, mappedSequenceFlows, bpmnModelBuilder);
    attachedTo.attachBoundaryEvent(boundaryEvent);
    return boundaryEvent;
  }

  private behavior.bpmn.events.BoundaryEvent getBoundaryEventWithDefinition(
      BoundaryEvent event, EventDefinition eventDefinition) {
    behavior.bpmn.events.BoundaryEvent boundaryEvent;
    // Create the boundary event.
    EventDefinitionVisitor<behavior.bpmn.events.BoundaryEvent> visitor =
        new EventDefinitionVisitor<>() {
          @Override
          public behavior.bpmn.events.BoundaryEvent handle(MessageEventDefinition evDefinition) {
            return new behavior.bpmn.events.BoundaryEvent(
                event.getId(),
                getFlowElementName(event),
                BoundaryEventType.MESSAGE,
                event.cancelActivity());
          }

          @Override
          public behavior.bpmn.events.BoundaryEvent handle(LinkEventDefinition evDefinition) {
            throw new BPMNRuntimeException("A boundary event cannot be a linked event!");
          }

          @Override
          public behavior.bpmn.events.BoundaryEvent handle(SignalEventDefinition evDefinition) {
            return new behavior.bpmn.events.BoundaryEvent(
                event.getId(),
                getFlowElementName(event),
                BoundaryEventType.SIGNAL,
                event.cancelActivity(),
                mapSignalEventDefinition(evDefinition, event));
          }

          @Override
          public behavior.bpmn.events.BoundaryEvent handle(TerminateEventDefinition evDefinition) {
            throw new BPMNRuntimeException("A boundary event cannot be a terminate event!");
          }

          @Override
          public behavior.bpmn.events.BoundaryEvent handle(TimerEventDefinition evDefinition) {
            return new behavior.bpmn.events.BoundaryEvent(
                event.getId(),
                getFlowElementName(event),
                BoundaryEventType.TIMER,
                event.cancelActivity());
          }

          @Override
          public behavior.bpmn.events.BoundaryEvent handle(ErrorEventDefinition evDefinition) {
            return new behavior.bpmn.events.BoundaryEvent(
                event.getId(),
                getFlowElementName(event),
                BoundaryEventType.ERROR,
                event.cancelActivity(),
                mapErrorEventDefinition(evDefinition));
          }

          @Override
          public behavior.bpmn.events.BoundaryEvent handle(EscalationEventDefinition evDefinition) {
            return new behavior.bpmn.events.BoundaryEvent(
                event.getId(),
                getFlowElementName(event),
                BoundaryEventType.ESCALATION,
                event.cancelActivity(),
                mapEscalationEventDefinition(evDefinition));
          }
        };
    boundaryEvent = this.visitDefinition(eventDefinition, visitor);
    return boundaryEvent;
  }

  private behavior.bpmn.events.definitions.EventDefinition mapEscalationEventDefinition(
      EscalationEventDefinition evDefinition) {
    if (evDefinition.getEscalation() != null
        && evDefinition.getEscalation().getEscalationCode() != null
        && !evDefinition.getEscalation().getEscalationCode().isBlank()) {
      return new behavior.bpmn.events.definitions.EscalationEventDefinition(
          evDefinition.getEscalation().getEscalationCode());
    }
    return behavior.bpmn.events.definitions.EventDefinition.empty();
  }

  private behavior.bpmn.events.definitions.EventDefinition mapErrorEventDefinition(
      ErrorEventDefinition evDefinition) {
    if (evDefinition.getError() != null
        && evDefinition.getError().getErrorCode() != null
        && !evDefinition.getError().getErrorCode().isBlank()) {
      return new behavior.bpmn.events.definitions.ErrorEventDefinition(
          evDefinition.getError().getErrorCode());
    }
    return behavior.bpmn.events.definitions.EventDefinition.empty();
  }

  private void handleEventSubProcess(
      SubProcess subprocess,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows,
      BPMNModelBuilder bpmnModelBuilder) {
    BPMNEventSubprocessBuilder subprocessBuilder =
        new BPMNEventSubprocessBuilder().name(getFlowElementName(subprocess));
    subprocess
        .getFlowElements()
        .forEach(
            flowElement ->
                mapFlowElement(
                    subprocessBuilder, mappedFlowNodes, mappedSequenceFlows, flowElement));

    bpmnModelBuilder.eventSubprocess(subprocessBuilder.build());
  }

  private CallActivity mapSubProcess(
      SubProcess subprocess,
      Map<String, behavior.bpmn.FlowNode> mappedFlowNodes,
      Map<String, Boolean> mappedSequenceFlows) {
    BPMNProcessBuilder subprocessBuilder =
        new BPMNProcessBuilder().name(getFlowElementName(subprocess));
    subprocess
        .getFlowElements()
        .forEach(
            flowElement ->
                mapFlowElement(
                    subprocessBuilder, mappedFlowNodes, mappedSequenceFlows, flowElement));

    CallActivity subProcessCallActivity =
        new CallActivity(subprocess.getId(), subprocessBuilder.build());
    mappedFlowNodes.put(subprocess.getId(), subProcessCallActivity);
    return subProcessCallActivity;
  }

  private boolean hasInstantiateCamundaProperty(FlowNode flowNode) {
    ExtensionElements extensionElements = flowNode.getExtensionElements();
    if (extensionElements == null) {
      return false;
    }
    // Instantiate is set as a camunda property using the camunda modeler.
    List<CamundaProperties> propertiesList =
        extensionElements.getElementsQuery().filterByType(CamundaProperties.class).list();

    return propertiesList.stream()
        .anyMatch(
            camundaProperties ->
                camundaProperties.getCamundaProperties().stream()
                    .anyMatch(
                        camundaProperty ->
                            camundaProperty.getCamundaName().equals("instantiate")
                                && camundaProperty.getCamundaValue().equals("true")));
  }

  private EndEvent mapEndEvent(FlowNode flowNode) {
    org.camunda.bpm.model.bpmn.instance.EndEvent endEvent =
        (org.camunda.bpm.model.bpmn.instance.EndEvent) flowNode;
    Collection<EventDefinition> eventDefinitions = endEvent.getEventDefinitions();
    if (eventDefinitions.isEmpty()) {
      return new EndEvent(flowNode.getId(), getFlowElementName(flowNode));
    }
    if (eventDefinitions.size() == 1) {
      EventDefinition eventDefinition = eventDefinitions.iterator().next();
      EventDefinitionVisitor<EndEvent> visitor =
          new EventDefinitionVisitor<>() {
            @Override
            public EndEvent handle(MessageEventDefinition evDefinition) {
              return new EndEvent(
                  flowNode.getId(), getFlowElementName(flowNode), EndEventType.MESSAGE);
            }

            @Override
            public EndEvent handle(LinkEventDefinition evDefinition) {
              throw new BPMNRuntimeException("End event definitions should not be of type link!");
            }

            @Override
            public EndEvent handle(SignalEventDefinition evDefinition) {
              return new EndEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  EndEventType.SIGNAL,
                  mapSignalEventDefinition(evDefinition, flowNode));
            }

            @Override
            public EndEvent handle(TerminateEventDefinition evDefinition) {
              return new EndEvent(
                  flowNode.getId(), getFlowElementName(flowNode), EndEventType.TERMINATION);
            }

            @Override
            public EndEvent handle(ErrorEventDefinition evDefinition) {
              return new EndEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  EndEventType.ERROR,
                  mapErrorEventDefinition(evDefinition));
            }

            @Override
            public EndEvent handle(EscalationEventDefinition evDefinition) {
              return new EndEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  EndEventType.ESCALATION,
                  mapEscalationEventDefinition(evDefinition));
            }

            @Override
            public EndEvent handle(TimerEventDefinition evDefinition) {
              throw new BPMNRuntimeException("End event definitions should not be of type timer!");
            }
          };
      return this.visitDefinition(eventDefinition, visitor);
    }
    throw new BPMNRuntimeException("Start event has more than one event definition!");
  }

  private StartEvent mapStartEvent(FlowNode flowNode) {
    org.camunda.bpm.model.bpmn.instance.StartEvent startEvent =
        (org.camunda.bpm.model.bpmn.instance.StartEvent) flowNode;
    Collection<EventDefinition> eventDefinitions = startEvent.getEventDefinitions();
    if (eventDefinitions.isEmpty()) {
      return new StartEvent(flowNode.getId(), getFlowElementName(flowNode));
    }
    if (eventDefinitions.size() == 1) {
      EventDefinition eventDefinition = eventDefinitions.iterator().next();
      EventDefinitionVisitor<StartEvent> visitor =
          new EventDefinitionVisitor<>() {
            @Override
            public StartEvent handle(MessageEventDefinition evDefinition) {
              return new StartEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  StartEventType.MESSAGE,
                  behavior.bpmn.events.definitions.EventDefinition.empty(),
                  startEvent.isInterrupting());
            }

            @Override
            public StartEvent handle(LinkEventDefinition evDefinition) {
              throw new BPMNRuntimeException("Start event definitions should not be of type link!");
            }

            @Override
            public StartEvent handle(SignalEventDefinition evDefinition) {
              return new StartEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  StartEventType.SIGNAL,
                  mapSignalEventDefinition(evDefinition, flowNode),
                  startEvent.isInterrupting());
            }

            @Override
            public StartEvent handle(TimerEventDefinition evDefinition) {
              throw new BPMNRuntimeException("Timer start events currently not supported!");
            }

            @Override
            public StartEvent handle(TerminateEventDefinition evDefinition) {
              throw new BPMNRuntimeException(
                  "Start event definitions should not be of type terminate!");
            }

            @Override
            public StartEvent handle(ErrorEventDefinition evDefinition) {
              return new StartEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  StartEventType.ERROR,
                  mapErrorEventDefinition(evDefinition),
                  startEvent.isInterrupting());
            }

            @Override
            public StartEvent handle(EscalationEventDefinition evDefinition) {
              return new StartEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  StartEventType.ESCALATION,
                  mapEscalationEventDefinition(evDefinition),
                  startEvent.isInterrupting());
            }
          };
      return this.visitDefinition(eventDefinition, visitor);
    }
    throw new BPMNRuntimeException("Start event has more than one event definition!");
  }

  private behavior.bpmn.events.definitions.SignalEventDefinition mapSignalEventDefinition(
      SignalEventDefinition evDefinition, FlowNode flowNode) {
    if (evDefinition.getSignal() != null
        && evDefinition.getSignal().getName() != null
        && !evDefinition.getSignal().getName().isBlank()) {
      return new behavior.bpmn.events.definitions.SignalEventDefinition(
          evDefinition.getSignal().getName());
    }
    return new behavior.bpmn.events.definitions.SignalEventDefinition(getFlowElementName(flowNode));
  }

  private behavior.bpmn.FlowNode mapIntermediateCatchEvent(FlowNode flowNode) {
    org.camunda.bpm.model.bpmn.instance.IntermediateCatchEvent intermediateCatchEvent =
        (org.camunda.bpm.model.bpmn.instance.IntermediateCatchEvent) flowNode;
    Collection<EventDefinition> eventDefinitions = intermediateCatchEvent.getEventDefinitions();
    if (eventDefinitions.isEmpty()) {
      throw new BPMNRuntimeException("Intermediate catch events need an event definition!");
    }
    if (eventDefinitions.size() == 1) {
      EventDefinition evDefinition = eventDefinitions.iterator().next();
      EventDefinitionVisitor<IntermediateCatchEvent> eventVisitor =
          new EventDefinitionVisitor<>() {
            @Override
            public IntermediateCatchEvent handle(MessageEventDefinition evDefinition) {
              return new IntermediateCatchEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  IntermediateCatchEventType.MESSAGE);
            }

            @Override
            public IntermediateCatchEvent handle(LinkEventDefinition evDefinition) {
              return new IntermediateCatchEvent(
                  flowNode.getId(), getFlowElementName(flowNode), IntermediateCatchEventType.LINK);
            }

            @Override
            public IntermediateCatchEvent handle(SignalEventDefinition evDefinition) {
              return new IntermediateCatchEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  IntermediateCatchEventType.SIGNAL,
                  mapSignalEventDefinition(evDefinition, flowNode));
            }

            @Override
            public IntermediateCatchEvent handle(TimerEventDefinition evDefinition) {
              return new IntermediateCatchEvent(
                  flowNode.getId(), getFlowElementName(flowNode), IntermediateCatchEventType.TIMER);
            }

            @Override
            public IntermediateCatchEvent handle(TerminateEventDefinition evDefinition) {
              throw new BPMNRuntimeException(
                  "Intermediate catch event definitions should not be of type terminate!");
            }

            @Override
            public IntermediateCatchEvent handle(ErrorEventDefinition evDefinition) {
              throw new BPMNRuntimeException(
                  "Intermediate catch event definitions should not be of type error!");
            }

            @Override
            public IntermediateCatchEvent handle(EscalationEventDefinition evDefinition) {
              throw new BPMNRuntimeException(
                  "Intermediate catch event definitions should not be of type escalation!");
            }
          };
      return this.visitDefinition(evDefinition, eventVisitor);
    }
    throw new BPMNRuntimeException("Intermediate catch event has more than one event definition!");
  }

  private behavior.bpmn.FlowNode mapIntermediateThrowEvent(FlowNode flowNode) {
    org.camunda.bpm.model.bpmn.instance.IntermediateThrowEvent intermediateThrowEvent =
        (org.camunda.bpm.model.bpmn.instance.IntermediateThrowEvent) flowNode;
    Collection<EventDefinition> eventDefinitions = intermediateThrowEvent.getEventDefinitions();
    if (eventDefinitions.isEmpty()) {
      return new IntermediateThrowEvent(
          flowNode.getId(), getFlowElementName(flowNode), IntermediateThrowEventType.NONE);
    }
    if (eventDefinitions.size() == 1) {
      EventDefinition evDefinition = eventDefinitions.iterator().next();
      EventDefinitionVisitor<IntermediateThrowEvent> eventVisitor =
          new EventDefinitionVisitor<>() {
            @Override
            public IntermediateThrowEvent handle(MessageEventDefinition evDefinition) {
              return new IntermediateThrowEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  IntermediateThrowEventType.MESSAGE);
            }

            @Override
            public IntermediateThrowEvent handle(LinkEventDefinition evDefinition) {
              return new IntermediateThrowEvent(
                  flowNode.getId(), getFlowElementName(flowNode), IntermediateThrowEventType.LINK);
            }

            @Override
            public IntermediateThrowEvent handle(SignalEventDefinition evDefinition) {
              return new IntermediateThrowEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  IntermediateThrowEventType.SIGNAL,
                  mapSignalEventDefinition(evDefinition, flowNode));
            }

            @Override
            public IntermediateThrowEvent handle(EscalationEventDefinition evDefinition) {
              return new IntermediateThrowEvent(
                  flowNode.getId(),
                  getFlowElementName(flowNode),
                  IntermediateThrowEventType.ESCALATION,
                  mapEscalationEventDefinition(evDefinition));
            }

            @Override
            public IntermediateThrowEvent handle(ErrorEventDefinition evDefinition) {
              throw new BPMNRuntimeException(
                  "Intermediate throw event definitions should not be of type error!");
            }

            @Override
            public IntermediateThrowEvent handle(TerminateEventDefinition evDefinition) {
              throw new BPMNRuntimeException(
                  "Intermediate throw event definitions should not be of type terminate!");
            }

            @Override
            public IntermediateThrowEvent handle(TimerEventDefinition evDefinition) {
              throw new BPMNRuntimeException(
                  "Intermediate throw event definitions should not be of type timer!");
            }
          };
      return this.visitDefinition(evDefinition, eventVisitor);
    }
    throw new BPMNRuntimeException("Intermediate throw event has more than one event definition!");
  }

  private <T> T visitDefinition(
      EventDefinition evDefinition,
      EventDefinitionVisitor<T> eventVisitor) {
    if (evDefinition instanceof MessageEventDefinition) {
      return eventVisitor.handle((MessageEventDefinition) evDefinition);
    }
    if (evDefinition instanceof LinkEventDefinition) {
      return eventVisitor.handle((LinkEventDefinition) evDefinition);
    }
    if (evDefinition instanceof SignalEventDefinition) {
      return eventVisitor.handle((SignalEventDefinition) evDefinition);
    }
    if (evDefinition instanceof TerminateEventDefinition) {
      return eventVisitor.handle((TerminateEventDefinition) evDefinition);
    }
    if (evDefinition instanceof TimerEventDefinition) {
      return eventVisitor.handle((TimerEventDefinition) evDefinition);
    }
    if (evDefinition instanceof ErrorEventDefinition) {
      return eventVisitor.handle((ErrorEventDefinition) evDefinition);
    }
    if (evDefinition instanceof EscalationEventDefinition) {
      return eventVisitor.handle((EscalationEventDefinition) evDefinition);
    }
    throw new BPMNRuntimeException("Unknown event definition found!" + evDefinition);
  }
}
