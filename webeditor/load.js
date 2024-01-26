
let modal = document.getElementById("loadModal");
let examples_list = document.getElementById("examples");
let modal_callback = null;
let lock = false;
let examples_dir = "examples/"
let list_path = examples_dir+"list.json";
let version_elt = document.getElementById("version");
let version_path = "version.txt";

function closeLoadModal(str) {
    modal.style.display = "none";
    if (modal_callback !== null)
        modal_callback(str);
}

let closeButton = document.getElementById("closeModal");
closeButton.onclick = function() {
    closeLoadModal(null);
}
window.onclick = function(event) {
  if (event.target == modal) {
    closeLoadModal(null);
  }
}

function getFile(url, success_callback) {
    lock = true;
    let xhr = new XMLHttpRequest();
    xhr.open("GET", url);
    xhr.setRequestHeader("Cache-Control", "no-cache, no-store, max-age=0");
    xhr.overrideMimeType("text/plain");
    xhr.addEventListener("readystatechange", () => {
        if (xhr.readyState == 4) {
            lock = false;
            if (xhr.status == 200)  {
                success_callback(xhr.responseText);
            } else {
                console.log("Unknown file " + url);
            }
        }
    });
    xhr.send();
};
getFile(list_path, (content) => {
    examples = JSON.parse(content);
    examples.forEach((element,index) => {
        let node = document.createElement('li');
        let link = document.createElement('a');
        link.appendChild(document.createTextNode(element["name"]));
        // link.title = ""; 
        link.href = "#";
        link.onclick = () => {
            if (!lock) getFile(examples_dir+element["path"], closeLoadModal);
        };
        node.appendChild(link);
        examples_list.appendChild(node);
    });
});

function showLoadModal(callback) {
    modal_callback = callback;
    modal.style.display = "block";
}

getFile(version_path, (content) => {
    version_elt.textContent = content;
});