# Overview
This is a prototype for DefSemTP, a tool for the formalization of the semantics of BPMN, and the verification of BPMN models via checking of temporal requirements. This prototype is created for my master's thesis, and is not yet implemented to it's full potential, only to the extent necessary to answer my research questions.

## Getting Started
- Clone the contents of this repository onto your computer.
- Add the business process model you would like to convert to Alloy into the src/benchmark models/ folder
- Open the main.java file from src/main/java/
- Enter the name of your BPMN file in the reader.printToAlloy method
- Run main
- Once complete, open the Alloy analyzer, and execute the model bpmn_model_substitutor.als
- If an instance is found, the model eventually completes and is safe.
