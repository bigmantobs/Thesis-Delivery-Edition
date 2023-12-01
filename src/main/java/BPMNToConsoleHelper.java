import behavior.bpmn.BPMNCollaboration;
import behavior.bpmn.reader.BPMNFileReader;

import java.io.File;
import java.util.function.UnaryOperator;

public interface BPMNToConsoleHelper {

  default BPMNCollaboration readModelFromResourceFolder(String resourceFileName) {
    String resourcePath = "src/testbpms/" + resourceFileName;
    return readModelFromResource(resourcePath);
  }

  default BPMNCollaboration readModelFromResourceFolder(
      String resourceFileName, UnaryOperator<String> elementNameTransformer) {
    String resourcePath = "src/testbpms/" + resourceFileName;
    return readModelFromResource(resourcePath, elementNameTransformer);
  }

  default BPMNCollaboration readModelFromResource(String resourcePath) {
    return readModelFromResource(resourcePath, elementName -> elementName);
  }

  default BPMNCollaboration readModelFromResource(
      String resourcePath, UnaryOperator<String> elementNameTransformer) {
    @SuppressWarnings("ConstantConditions")
    File model = new File(this.getClass().getResource(resourcePath).getFile());
    BPMNFileReader bpmnFileReader = new BPMNFileReader(elementNameTransformer);
    return bpmnFileReader.readModelFromFile(model);
  }
}
